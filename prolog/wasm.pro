nn(32).
nn(64).

sx(u).
sx(s).

iunop(clz).
iunop(ctz).
iunop(popcnt).

funop(abs).
funop(neg).
funop(sqrt).
funop(ceil).
funop(floor).
funop(trunc).
funop(nearest).

ibinop(add).
ibinop(sub).
ibinop(mul).
ibinop(div(SX)) :- sx(SX).
ibinop(rem(SX)) :- sx(SX).
ibinop(and).
ibinop(or).
ibinop(xor).
ibinop(shl).
ibinop(shr(SX)) :- sx(SX).
ibinop(rotl).
ibinop(rotr).

fbinop(add).
fbinop(sub).
fbinop(mul).
fbinop(div).
fbinop(min).
fbinop(max).
fbinop(copysign).

itestop(eqz).

instr([i,NN,const,X]) :- nn(NN), iconstant(NN,X).
instr([f,NN,const,X]) :- nn(NN), fconstant(NN,X).
instr([i,NN,O]) :- nn(NN), iunop(O).
instr([f,NN,O]) :- nn(NN), funop(O).
instr([i,NN,O]) :- nn(NN), ibinop(O).
instr([f,NN,O]) :- nn(NN), fbinop(O).
instr([i,NN,O]) :- nn(NN), itestop(O).

valid(C, [T,const,X], [], [T]) :- ctx(C), valuetype(T), constant(T,X).
valid(C, [T,O], [T], [T]) :- ctx(C), iunop(O), ivaluetype(T).
valid(C, [T,O], [T], [T]) :- ctx(C), funop(O), fvaluetype(T).
valid(C, [T,O], [T,T], [T]) :- ctx(C), ibinop(O), ivaluetype(T).
valid(C, [T,O], [T,T], [T]) :- ctx(C), fbinop(O), fvaluetype(T).
valid(C, [T,O], [T], [i32]) :- ctx(C), itestop(O), ivaluetype(T).
valid(C, [T,O], [T,T], [i32]) :- ctx(C), irelop(O), ivaluetype(T).
valid(C, [T,O], [T,T], [i32]) :- ctx(C), frelop(O), fvaluetype(T).
valid(C, [T2,O,T1,SX], [T1], [T2]) :- ctx(C), cvtop(O), valuetype(T1), valuetype(T2).

ctx(context).

valuetype(T) :- ivaluetype(T).
valuetype(T) :- fvaluetype(T).

ivaluetype(i32).
ivaluetype(i64).

fvaluetype(f32).
fvaluetype(f64).

iunop(clz).
iunop(ctz).
iunop(popcnt).
