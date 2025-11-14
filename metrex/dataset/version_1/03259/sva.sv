// SVA for mem_protect
// Concise, bindable, clockless (triggers on input changes)

`ifndef MEM_PROTECT_SVA_SV
`define MEM_PROTECT_SVA_SV

`ifndef SYNTHESIS

module mem_protect_sva #(
  parameter int n = 10,
  parameter int m = 2,
  parameter int memory_size = 1024
)(
  input logic [n-1:0] addr,
  input logic [m-1:0] ctrl,
  input logic         mem_en
);

  // Knownness only when inputs are known
  assert property (@(addr or ctrl)
                   !$isunknown({addr,ctrl}) |-> !$isunknown(mem_en))
    else $error("mem_en is X/Z with known inputs");

  // Golden functional equivalence
  property p_func;
    @(addr or ctrl)
      !$isunknown({addr,ctrl}) |-> (mem_en == ((addr < memory_size) && ctrl[0] && !ctrl[1]));
  endproperty
  assert property (p_func)
    else $error("mem_en functional mismatch");

  // One-sided safety checks (redundant but diagnostic-friendly)
  assert property (@(addr or ctrl) ctrl[1] |-> !mem_en)
    else $error("ctrl[1]==1 must force mem_en==0");

  assert property (@(addr or ctrl) !ctrl[0] |-> !mem_en)
    else $error("ctrl[0]==0 must force mem_en==0");

  assert property (@(addr or ctrl) (addr >= memory_size) |-> !mem_en)
    else $error("addr out of range must force mem_en==0");

  // Functional coverage
  cover property (@(addr or ctrl) (addr < memory_size) &&  ctrl[0] && !ctrl[1] &&  mem_en); // enabled
  cover property (@(addr or ctrl) (addr < memory_size) &&  ctrl[0] &&  ctrl[1] && !mem_en); // blocked by ctrl[1]
  cover property (@(addr or ctrl) (addr < memory_size) && !ctrl[0] && !ctrl[1] && !mem_en); // blocked by ctrl[0]
  cover property (@(addr or ctrl) (addr >= memory_size) && ctrl[0] && !ctrl[1] && !mem_en); // blocked by addr

  // Boundary coverage (hits if representable by addr width)
  cover property (@(addr or ctrl) (addr == memory_size-1) && ctrl[0] && !ctrl[1] && mem_en);
  cover property (@(addr or ctrl) (addr == memory_size)   && ctrl[0] && !ctrl[1] && !mem_en);
  cover property (@(addr or ctrl) (addr == '0)            && ctrl[0] && !ctrl[1] && mem_en);

endmodule

// Bind into DUT
bind mem_protect mem_protect_sva #(
  .n(n),
  .m(m),
  .memory_size(memory_size)
) mem_protect_sva_i (
  .addr(addr),
  .ctrl(ctrl),
  .mem_en(mem_en)
);

`endif // !SYNTHESIS
`endif // MEM_PROTECT_SVA_SV