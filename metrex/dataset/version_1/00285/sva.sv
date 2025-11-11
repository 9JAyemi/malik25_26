// SVA for xor_shift_register
module xor_shift_register_sva (
  input logic        clk,
  input logic        load,
  input logic [1:0]  ena,
  input logic [99:0] data,
  input logic [99:0] q,
  input logic        out_if_else
);

default clocking cb @(posedge clk); endclocking

// Combinational equivalence of out_if_else
assert property ( !$isunknown({q,data,out_if_else}) |-> (out_if_else == (|(q ^ data))) );

// Load has priority
assert property ( load |=> q == $past(data) );

// Rotate-left by 2 when enabled and not loading
assert property ( !load && (ena != 2'b00) |=> q == { $past(q[97:0]), $past(q[99:98]) } );

// Hold when disabled and not loading
assert property ( !load && (ena == 2'b00) |=> q == $past(q) );

// Coverage
cover property (load);                                 // load path
cover property (!load && (ena != 2'b00));              // rotate path
cover property (!load && (ena == 2'b00));              // hold path
cover property (!load && (ena != 2'b00) &&
                (q[1:0] == $past(q[99:98])));          // wrap-around into LSBs
cover property (!load && (ena != 2'b00) &&
                (q[99:2] == $past(q[97:0])));          // main body rotate
cover property (!$isunknown({q,data}) && (q == data)); // out_if_else expected 0 case
cover property (!$isunknown({q,data}) && (q != data)); // out_if_else expected 1 case
cover property (load && (ena != 2'b00));               // precedence when both active

endmodule

bind xor_shift_register xor_shift_register_sva sva_inst (.*);