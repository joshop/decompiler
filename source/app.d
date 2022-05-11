import std.stdio;
import std.algorithm;
import std.range;
import capstone;
import elf;
import std.format;
import std.array;
import std.conv;
import std.math;
enum Operator {
	ADD,
	SUBTRACT,
	MULTIPLY,
	DIVIDE,
	MODULO,
	AND,
	OR,
	NOT,
	LOGICALAND,
	LOGICALOR,
	LOGICALNOT,
	XOR,
	LEFTSHIFT,
	RIGHTSHIFT,
	DEREFERENCE,
	ATOMIC,
	INCREMENT,
	DECREMENT,
	EQUALS,
	NOTEQUALS,
	GREATER,
	LESS,
	GREATEREQUALS,
	LESSEQUALS,
	CAST,
	SIGNEXTEND,
	INDEXED,
	ADDRESS
}
bool precedenceOver(Operator inside, Operator outside) {
	Operator[][] precedence = [[Operator.LOGICALOR], [Operator.LOGICALAND], [Operator.OR], [Operator.XOR], [Operator.AND], [Operator.EQUALS, Operator.NOTEQUALS], [Operator.GREATER, Operator.LESS, Operator.GREATEREQUALS, Operator.LESSEQUALS], [Operator.LEFTSHIFT, Operator.RIGHTSHIFT], [Operator.ADD, Operator.SUBTRACT], [Operator.MULTIPLY, Operator.DIVIDE, Operator.MODULO], [Operator.INCREMENT, Operator.DECREMENT, Operator.LOGICALNOT, Operator.NOT, Operator.CAST, Operator.DEREFERENCE, Operator.SIGNEXTEND], [Operator.INDEXED], [Operator.ADDRESS]];
	foreach(i; 0..precedence.length) {
		if (precedence[i].canFind(inside) || precedence[i].canFind(outside)) {
			return !precedence[i].canFind(outside);
		}
	}
	return false;
}
string[Operator] opTexts;
ulong[] localAddresses;
enum AtomicTypes {
	GLOBAL,
	LOCAL,
	TEMPORARY
};
class Atomic {
	int size;
	bool isPointer;
	ulong value;
	AtomicTypes type;
	this(ulong value, int size, bool isPointer, AtomicTypes type) {
		this.size = size;
		this.value = value;
		this.isPointer = isPointer;
		this.type = type;
	}
	override string toString() {
		if (type == AtomicTypes.LOCAL) {
			if (!localAddresses.canFind(value)) localAddresses ~= value;
			return "local" ~ localAddresses.countUntil(value).to!string;
		}
		if (type == AtomicTypes.TEMPORARY) {
			return "temp" ~ value.to!string;
		}
		return "0x" ~ to!string(value, 16);
	}
	string typename() {
		return "uint" ~ to!string(size*8) ~ "_t" ~ (isPointer ? "*" : "");
	}
	bool mostlyEqual(Atomic other) {
		return value == other.value && type == other.type;
	}
	Atomic dup() {
		return new Atomic(value, size, isPointer, type);
	}
}
class Expression {
	Expression left;
	Expression right;
	Operator op;
	Atomic atomic;
	this(Atomic atomic) {
		this.atomic = atomic;
		this.op = Operator.ATOMIC;
	}
	this(Expression left, Operator op, Expression right) {
		this.left = left;
		this.op = op;
		this.right = right;
	}
	this(Expression left, int size, bool isPointer) {
		this.left = left;
		this.op = Operator.CAST;
		this.atomic = new Atomic(0, size, isPointer, AtomicTypes.GLOBAL);
	}
	override string toString() {
		if (op == Operator.ATOMIC) return atomic.toString();
		if (op == Operator.CAST) return "(" ~ atomic.typename() ~ ") " ~ left.toString();
		if (op == Operator.INDEXED) return left.toString() ~ "[" ~ right.toString() ~ "]";
		if (right is null) return opTexts[op] ~ " " ~ (precedenceOver(left.op, op) ? "(" : "") ~ left.toString() ~ (precedenceOver(left.op, op) ? ")" : "");
		return (precedenceOver(left.op, op) ? "(" : "") ~ left.toString() ~ (precedenceOver(left.op, op) ? ")" : "") ~ " " ~ opTexts[op] ~ " " ~ (precedenceOver(right.op, op) ? "(" : "") ~ right.toString() ~ (precedenceOver(right.op, op) ? ")" : "");
	}
	@property bool isPointer() {
		if (op == Operator.ATOMIC) return atomic.isPointer;
		if (right is null) return left.isPointer();
		return left.isPointer() || right.isPointer();
	}
	@property void isPointer(bool val) {
		if (op == Operator.ATOMIC) {
			atomic.isPointer = val;
			return;
		}
		left.isPointer = val;
		if (right is null) return;
		right.isPointer = val;
	}
	@property int size() {
		if (op == Operator.ATOMIC) return atomic.size;
		if (right is null) return left.size;
		return max(left.size, right.size);
	}
	string typename() {
		return "uint" ~ to!string(size*8) ~ "_t" ~ (isPointer ? "*" : "");
	}
	void beUsed() {
		if (left !is null) left.beUsed();
		if (right !is null) right.beUsed();
		if (op == Operator.ATOMIC && atomic.type == AtomicTypes.TEMPORARY) readTemps ~= atomic.value;
	}
	void clobber(Atomic kill, Atomic replace) {
		if (op == Operator.ATOMIC && atomic.mostlyEqual(kill)) {
			atomic = replace;
		} else {
			if (right !is null) right.clobber(kill, replace);
			if (left !is null) left.clobber(kill, replace);
		}
	}
	Expression dup() {
		if (op == Operator.ATOMIC) {
			return new Expression(atomic.dup);
		}
		return new Expression((left is null ? null : left.dup), op, (right is null ? null : right.dup));
	}
}
string[] decompStr;
class Statement {
	Statement dup() {
		assert(0);
	}
}
class AssignStatement : Statement {
	Expression destination;
	Expression source;
	this(Expression destination, Expression source) {
		this.destination = destination.dup;
		this.source = source.dup;
		if (destination.op != Operator.ATOMIC) return;
		int tempNum = usedTemps++;
		decomp ~= new TempBackupStatement(destination, tempNum);
		foreach (reg; state.byKeyValue) {
			if (reg.value is null) continue;
			reg.value.clobber(destination.atomic, new Atomic(tempNum, 8, false, AtomicTypes.TEMPORARY));
		}
	}
	override string toString() {
		return destination.toString() ~ " = " ~ source.toString() ~ ";";
	}
}
class FunctionCallStatement : Statement {
	string fxname;
	int temp;
	Expression[] args;
	this(string fxname, int temp, Expression[] args) {
		this.fxname = fxname;
		this.temp = temp;
		this.args = args;
	}
	override string toString() {
		return (readTemps.canFind(temp) ? "temp" ~ temp.to!string ~ " = " : "") ~ fxname ~ "(" ~ args.map!(to!string).join(", ") ~ ");";
	}
}
class ReturnStatement : Statement {
	Expression value;
	this(Expression value) {
		this.value = value;
	}
	override string toString() {
		return "return " ~ value.to!string ~ ";";
	}
}
class TempBackupStatement : Statement {
	Expression source;
	int temp;
	this(Expression source, int temp) {
		this.source = source;
		this.temp = temp;
	}
	override string toString() {
		if (readTemps.canFind(temp)) return "temp" ~ temp.to!string ~ " = " ~ source.toString() ~ ";";
		return "";
	}
}
Expression[X86RegisterId] state;
Statement[] decomp;
ulong curAddress;
Expression fromOp(const(X86Op) op) {
	if (op.type == X86OpType.imm) {
		return new Expression(new Atomic(op.imm, op.size, false, AtomicTypes.GLOBAL));
	} else if (op.type == X86OpType.reg) {
		return register(op.reg.id);
	} else if (op.type == X86OpType.mem) {
		if (op.mem.base.id == X86RegisterId.invalid && op.mem.index.id == X86RegisterId.invalid) {
			return new Expression(new Atomic(op.mem.disp, op.size, true, AtomicTypes.GLOBAL));
		}
		if (op.mem.base.id == X86RegisterId.rbp && op.mem.index.id == X86RegisterId.invalid) {
			return new Expression(new Atomic(op.mem.disp, op.size, false, AtomicTypes.LOCAL));
		}
		if (op.mem.base.id == X86RegisterId.rip && op.mem.index.id == X86RegisterId.invalid) {
			return new Expression(new Atomic(op.mem.disp + curAddress, op.size, true, AtomicTypes.GLOBAL));
		}
		if (op.mem.base.id == X86RegisterId.rbp && op.mem.index.id != X86RegisterId.invalid) {
			// TODO local size and stuff
			return new Expression(new Expression(new Atomic(op.mem.disp, op.size, false, AtomicTypes.LOCAL)), Operator.INDEXED, state[op.mem.index.id]);
		}
		if (op.mem.base.id != X86RegisterId.invalid && op.mem.index.id != X86RegisterId.invalid && op.size == state[op.mem.base.id].size) {
			return new Expression(state[op.mem.base.id], Operator.INDEXED, state[op.mem.index.id]);
		}
		if (op.mem.base.id != X86RegisterId.invalid && op.mem.index.id == X86RegisterId.invalid && op.size == register(op.mem.base.id).size) {
			return new Expression(register(op.mem.base.id), Operator.INDEXED, new Expression(new Atomic(op.mem.disp, op.size, false, AtomicTypes.GLOBAL)));
		}
	}
	assert(0);
}
void toOp(const(X86Op) op, Expression from) {
	if (op.type == X86OpType.reg) {
		toOp(op.reg.id, from);
	} else {
		decomp ~= new AssignStatement(fromOp(op), from);
		// TODO dumping
	}
}
void toOp(X86RegisterId id, Expression from) {
	state[id] = from;
	foreach (lowLong; lowLongs.byKeyValue) {
		if (lowLong.value == id) {
			state[lowLong.key] = from;
		}
		if (lowLong.key == id) {
			state[lowLong.value] = from;
		}
	}
}
X86RegisterId[X86RegisterId] lowLongs;
X86RegisterId[X86RegisterId] lowWords;
Operator[X86InstructionId] instrOperators;
Expression register(X86RegisterId reg) {
	if (reg in state) return state[reg];
	if (reg in lowLongs && lowLongs[reg] in state) return state[lowLongs[reg]];
	if (reg in lowWords && lowWords[reg] in state) return state[lowWords[reg]];
	if (reg in lowLongs && lowLongs[reg] in lowWords && lowWords[lowLongs[reg]] in state) return state[lowWords[lowLongs[reg]]];
	return null;
}
Expression[] stack;
int usedTemps = 0;
ulong[] readTemps;
Expression cmpExpression1, cmpExpression2;
enum JumpCondition {
	UNCONDITIONAL,
	LESS,
	GREATER,
	LESSEQUAL,
	GREATEREQUAL,
	EQUAL,
	NOTEQUAL
}
class Unfinished {
	X86Instruction[] pre;
	Statement[] post;
	bool finished;
	this (X86Instruction[] pre, Statement[] post) {
		this.pre = pre;
		this.post = post;
	}
	this () {
		
	}
	void debugPrint() {
		foreach (inst; pre) {
			writefln!"%10x: %-30s %-8s %s"(inst.address, inst.bytes().map!(a => format!"%02x"(a)).join(' '), inst.mnemonic(), inst.opStr());
		}
	}
}
class UnfinishedIfElse : Unfinished {
	X86Instruction[] elsePre;
	Statement[] elsePost;
	JumpCondition condition;
	this (Unfinished doIf, Unfinished doElse, JumpCondition condition) {
		pre = doIf.pre.dup;
		elsePre = doElse.pre.dup;
		this.condition = condition;
	}
	override void debugPrint() {
		writefln!"if (%s) {"(condition);
		super.debugPrint();
		writefln!"} else {";
		foreach (inst; elsePre) {
			writefln!"%10x: %-30s %-8s %s"(inst.address, inst.bytes().map!(a => format!"%02x"(a)).join(' '), inst.mnemonic(), inst.opStr());
		}
		writefln!"}";
	}
}
class UnfinishedPair : Unfinished {
	Unfinished after;
	Unfinished before;
	this (Unfinished first, Unfinished second) {
		before = first;
		after = second;
	}
	override void debugPrint() {
		before.debugPrint();
		after.debugPrint();
	}
}
class Cfg {
	Cfg ifTrue;
	Cfg ifFalse;
	ulong addressIfTrue;
	ulong addressIfFalse;
	ulong address;
	Unfinished code;
	JumpCondition cond;
	ulong index;
	this(X86Instruction[] code, JumpCondition cond, ulong address) {
		this.code = new Unfinished(code, []);
		this.cond = cond;
		ifTrue = null;
		ifFalse = null;
		this.address = address;
		index = cfg.length + 1;
	}
	void bifurcate(ulong along) {
		Cfg lower = new Cfg([], cond, along);
		X86Instruction[] myNew;
		foreach (inst; code.pre) {
			if (inst.address >= along) {
				lower.code.pre ~= inst;
			} else {
				myNew ~= inst;
			}
		}
		code.pre = myNew;
		lower.addressIfTrue = addressIfTrue;
		lower.addressIfFalse = addressIfFalse;
		addressIfTrue = along;
		cond = JumpCondition.UNCONDITIONAL;
		cfg ~= lower;
	}
	bool bodyContainsAddr(ulong addr) {
		ulong cur = address;
		foreach (inst; code.pre) {
			cur += inst.bytes().length;
			if (cur == addr) return true;
		}
		return false;
	}
	bool performIfElseTransform() {
		// conditions for ifElseTransform
		// - ifTrue and ifFalse are both unconditional
		// - ifTrue and ifFalse both have the same ifTrue
		if (ifTrue is null || ifFalse is null) return false;
		if (ifTrue.cond != JumpCondition.UNCONDITIONAL || ifFalse.cond != JumpCondition.UNCONDITIONAL || ifTrue.ifTrue != ifFalse.ifTrue) return false;
		UnfinishedIfElse end = new UnfinishedIfElse(ifTrue.code, ifFalse.code, cond);
		cond = JumpCondition.UNCONDITIONAL;
		ifTrue.code = end;
		ifFalse.index = 0;
		ifFalse = null;
		return true;
	}
	bool performBlockTransform() {
		// conditions for blockTransform
		// - this is unconditional
		if (ifTrue is null) return false;
		if (cond != JumpCondition.UNCONDITIONAL) return false;
		UnfinishedPair end = new UnfinishedPair(code, ifTrue.code);
		code = end;
		ifTrue.index = 0;
		cond = ifTrue.cond;
		ifFalse = ifTrue.ifFalse;
		ifTrue = ifTrue.ifTrue;
		return true;
	}
}
Cfg[] cfg;
void main(string[] argv) {
	ELF elf = ELF.fromFile(argv[1]);
	ELFSection sec = elf.getSection(".symtab").get;
	ELFSymbol symbol = SymbolTable(sec).symbols().find!(a => a.name == argv[2]).front;
	auto elfFile = File(argv[1]);
	elfFile.seek(symbol.value);
	auto code = elfFile.rawRead(new ubyte[symbol.size]);
	auto disasm = new CapstoneX86(ModeFlags(Mode.bit64));
	disasm.syntax = Syntax.att;
	disasm.detail = true;
	auto assembly = disasm.disasm(code, symbol.value);
	opTexts = [Operator.ADD: "+", Operator.SUBTRACT: "-", Operator.XOR: "^", Operator.ATOMIC: " ", Operator.SIGNEXTEND: "signextend", Operator.ADDRESS: "address", Operator.MULTIPLY: "*"];
	lowLongs = [X86RegisterId.rax : X86RegisterId.eax, X86RegisterId.rdi : X86RegisterId.edi, X86RegisterId.rsi : X86RegisterId.esi, X86RegisterId.rdx : X86RegisterId.edx];
	lowWords = [X86RegisterId.eax : X86RegisterId.ax];
	instrOperators = [X86InstructionId.add : Operator.ADD, X86InstructionId.sub : Operator.SUBTRACT, X86InstructionId.xor : Operator.XOR, X86InstructionId.cdqe : Operator.SIGNEXTEND, X86InstructionId.imul : Operator.MULTIPLY];
	Cfg curCfg = new Cfg([], JumpCondition.UNCONDITIONAL, symbol.value);
	X86Instruction[] buffer;
	JumpCondition[X86InstructionId] jumpTypes = [X86InstructionId.jle : JumpCondition.LESSEQUAL, X86InstructionId.jmp : JumpCondition.UNCONDITIONAL];
	foreach (inst; assembly) {
		if (cast(X86InstructionId)inst.idAsInt() in jumpTypes) {
			curCfg.cond = jumpTypes[cast(X86InstructionId)inst.idAsInt()];
			ulong jumpTarget = inst.detail().operands.front.imm;
			curCfg.addressIfTrue = jumpTarget;
			curCfg.addressIfFalse = inst.address + inst.bytes().length;
			cfg ~= curCfg;
			curCfg = new Cfg([], JumpCondition.UNCONDITIONAL, inst.address + inst.bytes().length);
		} else {
			curCfg.code.pre ~= inst;
		}
	}
	cfg ~= curCfg;
	foreach (node; cfg) {
		auto needSplit = cfg.find!(a => a.bodyContainsAddr(node.addressIfTrue));
		if (!needSplit.empty) needSplit.front.bifurcate(node.addressIfTrue);
		if (node.cond == JumpCondition.UNCONDITIONAL) break;
		needSplit = cfg.find!(a => a.bodyContainsAddr(node.addressIfFalse));
		if (!needSplit.empty) needSplit.front.bifurcate(node.addressIfFalse);
	}
	foreach (node; cfg) {
		foreach (other; cfg) {
			if (other.address == node.addressIfTrue) node.ifTrue = other;
			if (other.address == node.addressIfFalse) node.ifFalse = other;
		}
	}
	outer: while (true) {
		cfg = cfg.filter!(a => a.index).array;
		/*foreach (node; cfg) {
			writefln!"------------------------------";
			writefln!"Cfg node %d at %x"(node.index, node.address);
			if (node.cond == JumpCondition.UNCONDITIONAL) {
				writefln!"Always %x"(node.ifTrue is null ? 0 : node.ifTrue.address);
			} else {
				writefln!"If %s, %x else %x"(node.cond, node.ifTrue is null ? 0 : node.ifTrue.address, node.ifFalse is null ? 0 : node.ifFalse.address);
			}
			writefln!"------------------------------";
			node.code.debugPrint();
			writefln!"------------------------------\n";
		}*/
		// attempt ifelse
		foreach (index; 0..cfg.length) {
			if (cfg[index].performIfElseTransform()) continue outer;
		}
		// attempt block
		foreach (index; 0..cfg.length) {
			if (cfg[index].performBlockTransform()) continue outer;
		}
		break;
	}
	foreach (node; cfg) {
		writefln!"------------------------------";
		writefln!"Cfg node %d at %x"(node.index, node.address);
		if (node.cond == JumpCondition.UNCONDITIONAL) {
			writefln!"Always %x"(node.ifTrue is null ? 0 : node.ifTrue.address);
		} else {
			writefln!"If %s, %x else %x"(node.cond, node.ifTrue is null ? 0 : node.ifTrue.address, node.ifFalse is null ? 0 : node.ifFalse.address);
		}
		writefln!"------------------------------";
		node.code.debugPrint();
		writefln!"------------------------------\n";
	}
	return;
	foreach (inst; assembly) {
		writefln!"%10x: %-30s %-8s %s"(inst.address, inst.bytes().map!(a => format!"%02x"(a)).join(' '), inst.mnemonic(), inst.opStr());
		curAddress = inst.address + inst.bytes().length;
		switch(inst.idAsInt()) {
			case X86InstructionId.mov:
				// mov
				// source: register, immediate, or memory
				Expression source;
				auto opSources = inst.detail().operands.filter!(a => a.access & AccessType.read || a.type == X86OpType.imm).array;
				assert(opSources.length == 1);
				source = fromOp(opSources.front);
				if (source !is null) source.beUsed();
				auto opDests = inst.detail().operands.filter!(a => a.access & AccessType.write).array;
				toOp(opDests.front, source);
				break;
			case X86InstructionId.add:
			case X86InstructionId.sub:
			case X86InstructionId.xor:
			case X86InstructionId.imul:
				auto opSources = inst.detail().operands.filter!(a => a.access & AccessType.read || a.type == X86OpType.imm).array;
				assert(opSources.length == 2);
				Expression source1 = fromOp(opSources.front);
				if (source1 !is null) source1.beUsed();
				Expression source2 = fromOp(opSources[1]);
				if (source2 !is null) source2.beUsed();
				auto opDests = inst.detail().operands.filter!(a => a.access & AccessType.write).array;
				if (inst.idAsInt() == X86InstructionId.imul) {
					auto temp = source1;
					source1 = source2;
					source2 = temp;
				}
				if (inst.idAsInt() == X86InstructionId.xor && source1 == source2) {
					toOp(opDests.front, new Expression(new Atomic(0, opSources.front.size, false, AtomicTypes.GLOBAL)));
				} else {
					toOp(opDests.front, new Expression(source2, instrOperators[cast(X86InstructionId)inst.idAsInt()], source1));
				}
				break;
			case X86InstructionId.lea:
				Expression source;
				auto opSources = inst.detail().operands.filter!(a => a.access & AccessType.read || a.type == X86OpType.imm).array;
				assert(opSources.length == 1);
				source = fromOp(opSources.front);
				if (!source.isPointer) {
					source = new Expression(source, Operator.ADDRESS, null);
				}
				source.isPointer = false;
				auto opDests = inst.detail().operands.filter!(a => a.access & AccessType.write).array;
				toOp(opDests.front, source);
				break;
			case X86InstructionId.call:
				int tempNum = usedTemps++;
				auto fx = SymbolTable(sec).symbols().find!(a => a.value == inst.detail().operands[0].imm);
				string fxcall;
				if (fx.empty || fx.front.type != 2) {
					fxcall = "func_" ~ inst.detail().operands[0].imm.to!string(16);
				} else {
					fxcall = fx.front.name;
				}
				Expression[] args;
				foreach(argReg; [X86RegisterId.rdi, X86RegisterId.rsi, X86RegisterId.rdx]) {
					if (register(argReg) is null) break;
					args ~= register(argReg);
				}
				decomp ~= new FunctionCallStatement(fxcall, tempNum, args);
				toOp(X86RegisterId.rax, new Expression(new Atomic(tempNum, 8, false, AtomicTypes.TEMPORARY)));
				break;
			case X86InstructionId.ret:
				decomp ~= new ReturnStatement(register(X86RegisterId.rax));
				break;
			case X86InstructionId.push:
				Expression source;
				auto opSources = inst.detail().operands.filter!(a => a.access & AccessType.read || a.type == X86OpType.imm).array;
				assert(opSources.length == 1);
				source = fromOp(opSources.front);
				stack ~= source;
				break;
			case X86InstructionId.pop:
				auto opDests = inst.detail().operands.filter!(a => a.access & AccessType.write).array;
				toOp(opDests.front, stack[$-1]);
				stack.remove(stack.length-1);
				break;
			case X86InstructionId.cdqe:
				Expression source = state[X86RegisterId.rax];
				auto opDests = inst.detail().operands.filter!(a => a.access & AccessType.write).array;
				toOp(X86RegisterId.rax, new Expression(source, instrOperators[cast(X86InstructionId)inst.idAsInt()], null));
				break;
			case X86InstructionId.leave:
			case X86InstructionId.endbr64:
				break;
			case X86InstructionId.cmp:
				auto opSources = inst.detail().operands.filter!(a => a.access & AccessType.read || a.type == X86OpType.imm).array;
				assert(opSources.length == 2);
				cmpExpression1 = fromOp(opSources[0]);
				cmpExpression2 = fromOp(opSources[1]);
				break;
			default: 
			writefln!"No instruction: %s"(inst.mnemonic);
			assert(0);
		}
	}
	writeln("\n-----------------\n");
	writeln(decomp.map!(to!string).filter!(a => a.length).join('\n'));
}
