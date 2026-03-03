// SVA checker for shift_nor
module shift_nor_sva #(parameter int WIDTH = 100)
(
  input  logic                 clk,
  input  logic                 load,
  input  logic [1:0]           ena,
  input  logic [WIDTH-1:0]     data,
  input  logic                 a,
  input  logic                 b,
  input  logic                 out,
  input  logic [WIDTH-1:0]     shifted_data,
  input  logic [WIDTH-1:0]     shift_reg
);
  localparam int MSB = WIDTH-1;

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Functional correctness
  assert property (load |=> shift_reg == $past(data));

  assert property (!load && (ena == 2'b01)
                   |=> shift_reg == {$past(shift_reg[0]), $past(shift_reg[MSB:1])});

  assert property (!load && (ena == 2'b10)
                   |=> shift_reg == {$past(shift_reg[MSB-1:0]), $past(shift_reg[MSB])});

  assert property (!load && !(ena inside {2'b01,2'b10})
                   |=> shift_reg == $past(shift_reg));

  // No spurious updates
  assert property ($changed(shift_reg)
                   |-> $past(load || (ena inside {2'b01,2'b10})));

  // Alias check
  assert property (shifted_data === shift_reg);

  // NOR gate correctness
  assert property (out === ~(a | b));

  // Coverage
  cover property (load);
  cover property (!load && ena == 2'b01);
  cover property (!load && ena == 2'b10);
  cover property (!load && !(ena inside {2'b01,2'b10}));

  // Wrap-around coverage
  cover property (!load && ena == 2'b01 |=> shift_reg[MSB] == $past(shift_reg[0]));
  cover property (!load && ena == 2'b10 |=> shift_reg[0]   == $past(shift_reg[MSB]));

  // NOR truth table coverage
  cover property (a==0 && b==0 && out==1);
  cover property (a==0 && b==1 && out==0);
  cover property (a==1 && b==0 && out==0);
  cover property (a==1 && b==1 && out==0);

endmodule

// Bind the checker into the DUT scope (gains access to internal shift_reg)
bind shift_nor shift_nor_sva #(.WIDTH(100)) shift_nor_sva_i (.*);