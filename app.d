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
class Atomic {
	int size;
	bool isPointer;
	ulong value;
	bool local;
	this(ulong value, int size, bool isPointer, bool local) {
		this.size = size;
		this.value = value;
		this.isPointer = isPointer;
		this.local = local;
	}
	override string toString() {
		if (local) {
			if (!localAddresses.canFind(value)) localAddresses ~= value;
			return "local" ~ localAddresses.countUntil(value).to!string;
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
		this.atomic = new Atomic(0, size, isPointer, false);
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
}
Expression[X86RegisterId] state;
string[] decomp;
ulong curAddress;
Expression fromOp(const(X86Op) op) {
	if (op.type == X86OpType.imm) {
		return new Expression(new Atomic(op.imm, op.size, false, false));
	} else if (op.type == X86OpType.reg) {
		return register(op.reg.id);
	} else if (op.type == X86OpType.mem) {
		if (op.mem.base.id == X86RegisterId.invalid && op.mem.index.id == X86RegisterId.invalid) {
			return new Expression(new Atomic(op.mem.disp, op.size, true, false));
		}
		if (op.mem.base.id == X86RegisterId.rbp && op.mem.index.id == X86RegisterId.invalid) {
			return new Expression(new Atomic(op.mem.disp, op.size, false, true));
		}
		if (op.mem.base.id == X86RegisterId.rip && op.mem.index.id == X86RegisterId.invalid) {
			return new Expression(new Atomic(op.mem.disp + curAddress, op.size, true, false));
		}
		if (op.mem.base.id == X86RegisterId.rbp && op.mem.index.id != X86RegisterId.invalid) {
			// TODO local size and stuff
			return new Expression(new Expression(new Atomic(op.mem.disp, op.size, false, true)), Operator.INDEXED, state[op.mem.index.id]);
		}
		if (op.mem.base.id != X86RegisterId.invalid && op.mem.index.id != X86RegisterId.invalid && op.size == state[op.mem.base.id].size) {
			return new Expression(state[op.mem.base.id], Operator.INDEXED, state[op.mem.index.id]);
		}
		writeln(register(X86RegisterId.rax));
		if (op.mem.base.id != X86RegisterId.invalid && op.mem.index.id == X86RegisterId.invalid && op.size == register(op.mem.base.id).size) {
			writeln(new Expression(register(op.mem.base.id), Operator.INDEXED, new Expression(new Atomic(op.mem.disp, op.size, false, false))));
			return new Expression(register(op.mem.base.id), Operator.INDEXED, new Expression(new Atomic(op.mem.disp, op.size, false, false)));
		}
	}
	assert(0);
}
void toOp(const(X86Op) op, Expression from) {
	if (op.type == X86OpType.reg) {
		toOp(op.reg.id, from);
	} else {
		decomp ~= fromOp(op).toString() ~ " = " ~ from.toString() ~ ";";
		// TODO dumping
	}
}
void toOp(X86RegisterId id, Expression from) {
	state[id] = from;
	foreach (lowLong; lowLongs.byKeyValue) {
		if (lowLong.value == id) {
			state[lowLong.key] = from;
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
	lowLongs = [X86RegisterId.rax : X86RegisterId.eax, X86RegisterId.rdi : X86RegisterId.edi, X86RegisterId.rsi : X86RegisterId.esi];
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
				Expression source2 = fromOp(opSources[1]);
				auto opDests = inst.detail().operands.filter!(a => a.access & AccessType.write).array;
				if (inst.idAsInt() == X86InstructionId.xor && source1 == source2) {
					toOp(opDests.front, new Expression(new Atomic(0, opSources.front.size, false, false)));
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
				string fxcall;
				auto fx = SymbolTable(sec).symbols().find!(a => a.value == inst.detail().operands[0].imm);
				if (fx.empty || fx.front.type != 2) {
					fxcall = "func_" ~ inst.detail().operands[0].imm.to!string(16) ~ "(";
				} else {
					fxcall = fx.front.name ~ "(";
				}
				foreach(argReg; [X86RegisterId.rdi, X86RegisterId.rsi]) {
					if (register(argReg) is null) break;
					fxcall ~= register(argReg).toString() ~ ", ";
				}
				decomp ~= fxcall[0..$-2] ~ ");";
				break;
			case X86InstructionId.ret:
				decomp ~= "return " ~ register(X86RegisterId.rax).toString() ~ ";";
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
	writeln(decomp.join('\n'));
}