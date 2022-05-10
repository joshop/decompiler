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
	Operator[][] precedence = [[Operator.LOGICALOR], [Operator.LOGICALAND], [Operator.OR], [Operator.XOR], [Operator.AND], [Operator.EQUALS, Operator.NOTEQUALS], [Operator.GREATER, Operator.LESS, Operator.GREATEREQUALS, Operator.LESSEQUALS], [Operator.LEFTSHIFT, Operator.RIGHTSHIFT], [Operator.ADD, Operator.SUBTRACT], [Operator.MULTIPLY, Operator.DIVIDE, Operator.MODULO], [Operator.INCREMENT, Operator.DECREMENT, Operator.LOGICALNOT, Operator.NOT, Operator.CAST, Operator.DEREFERENCE, Operator.ADDRESS, Operator.SIGNEXTEND], [Operator.INDEXED]];
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
		if (right is null) return opTexts[op] ~ " " ~ left.toString();
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
}
string[] decompStr;
class Statement {
	
}
class AssignStatement : Statement {
	Expression destination;
	Expression source;
	this(Expression destination, Expression source) {
		this.destination = destination;
		this.source = source;
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
		writeln(register(X86RegisterId.rax));
		if (op.mem.base.id != X86RegisterId.invalid && op.mem.index.id == X86RegisterId.invalid && op.size == register(op.mem.base.id).size) {
			writeln(new Expression(register(op.mem.base.id), Operator.INDEXED, new Expression(new Atomic(op.mem.disp, op.size, false, AtomicTypes.GLOBAL))));
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
	foreach (inst; assembly) {
		writefln!"%10x: %-20s %-8s %s"(inst.address, inst.bytes().map!(a => format!"%02x"(a)).join(' '), inst.mnemonic(), inst.opStr());
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
				writeln(register(X86RegisterId.eax));
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
			default: 
			writefln!"No instruction: %d"(inst.idAsInt());
			assert(0);
		}
	}
	writeln("\n-----------------\n");
	writeln(decomp.map!(to!string).join('\n'));
}
