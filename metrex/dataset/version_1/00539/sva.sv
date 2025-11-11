// SVA for logic_function
// Bind these assertions to the DUT

module logic_function_sva (
  input logic x,
  input logic y,
  input logic z,
  input logic out1,
  input logic out2
);

  // Functional correctness when inputs are known
  property p_out1_func;
    @(x or y or z) !$isunknown({x,y,z}) |-> (out1 == ((x & y) | !z));
  endproperty
  a_out1_func: assert property (p_out1_func);

  property p_out2_func;
    @(x or y or z) !$isunknown({x,y,z}) |-> (out2 == ((!x & y) | z));
  endproperty
  a_out2_func: assert property (p_out2_func);

  // Sanity: outputs should never be X/Z when inputs are known
  a_out1_known: assert property (@(x or y or z) !$isunknown({x,y,z}) |-> !$isunknown(out1));
  a_out2_known: assert property (@(x or y or z) !$isunknown({x,y,z}) |-> !$isunknown(out2));

  // Input-space coverage (exercise full truth table)
  cover property (@(x or y or z) {x,y,z} == 3'b000);
  cover property (@(x or y or z) {x,y,z} == 3'b001);
  cover property (@(x or y or z) {x,y,z} == 3'b010);
  cover property (@(x or y or z) {x,y,z} == 3'b011);
  cover property (@(x or y or z) {x,y,z} == 3'b100);
  cover property (@(x or y or z) {x,y,z} == 3'b101);
  cover property (@(x or y or z) {x,y,z} == 3'b110);
  cover property (@(x or y or z) {x,y,z} == 3'b111);

  // Output toggle coverage
  cover property (@(posedge out1) 1'b1);
  cover property (@(negedge out1) 1'b1);
  cover property (@(posedge out2) 1'b1);
  cover property (@(negedge out2) 1'b1);

endmodule

bind logic_function logic_function_sva sva (
  .x(x), .y(y), .z(z),
  .out1(out1), .out2(out2)
);