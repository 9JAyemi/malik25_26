// SVA for dataprocessor
module dataprocessor_sva(
  input logic        clk,
  input logic        reset,
  input logic [9:0]  datain,
  input logic [9:0]  dataout,
  input logic        validout
);

  localparam int THRESH = 10'd100;

  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Basic known-value checks
  assert property (!$isunknown({dataout, validout}));
  assert property (!reset |-> !$isunknown(datain));

  // Synchronous reset behavior
  assert property (reset |-> (dataout == 10'd0 && validout == 1'b0));

  // Next-state mapping (priority reset)
  assert property ($past(reset) |-> (dataout == 10'd0 && validout == 1'b0));
  assert property (!$past(reset) && ($past(datain) >= THRESH)
                   |-> (dataout == $past(datain) && validout == 1'b1));
  assert property (!$past(reset) && ($past(datain) < THRESH)
                   |-> (dataout == 10'd0 && validout == 1'b0));

  // Output consistency
  assert property (validout
                   |-> (!$past(reset) && $past(datain) >= THRESH
                        && dataout == $past(datain)));
  assert property (!validout |-> (dataout == 10'd0));

  // Coverage
  cover property (reset ##1 !reset);
  cover property ((!reset && datain == THRESH) |=> (validout && dataout == $past(datain)));
  cover property ((!reset && datain == (THRESH-1)) |=> (!validout && dataout == 10'd0));
  cover property ((!reset && datain < THRESH) ##1 (!reset && datain >= THRESH));  // 0->1 transition
  cover property ((!reset && datain >= THRESH) ##1 (!reset && datain < THRESH));  // 1->0 transition
  cover property (((!reset && datain >= THRESH)) [*2]);                            // back-to-back valid

endmodule

// Bind into DUT
bind dataprocessor dataprocessor_sva u_dataprocessor_sva (.*);