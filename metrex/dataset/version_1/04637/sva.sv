// Concise SVA bind for soc_design_SystemID
module soc_design_SystemID_sva (
  input logic         clock,
  input logic         reset_n,
  input logic [31:0]  address,
  input logic [31:0]  readdata
);
  default clocking cb @(posedge clock); endclocking

  // No X/Z on critical signals
  assert property (@cb !$isunknown(reset_n));
  assert property (@cb !$isunknown(readdata));
  assert property (@cb disable iff (!reset_n) !$isunknown(address));

  // Asynchronous reset drives 0 immediately and while low
  assert property (@(negedge reset_n) ##0 (readdata == 32'h0000_0000));
  assert property (@cb !reset_n |-> (readdata == 32'h0000_0000));

  // Functional mapping: next-cycle value equals function of current address
  assert property (@cb disable iff (!reset_n)
                   (address == 32'h0000_0000) |=> (readdata == 32'h0000_00FF));
  assert property (@cb disable iff (!reset_n)
                   (address != 32'h0000_0000) |=> (readdata == 32'h590D_8D31));

  // Output range when out of reset
  assert property (@cb disable iff (!reset_n)
                   readdata inside {32'h0000_00FF, 32'h590D_8D31});

  // Coverage: reset pulse, both address cases, both output values and transitions
  cover property (@cb !reset_n ##1 reset_n);
  cover property (@cb disable iff (!reset_n)
                  (address == 32'h0000_0000) |=> (readdata == 32'h0000_00FF));
  cover property (@cb disable iff (!reset_n)
                  (address != 32'h0000_0000) |=> (readdata == 32'h590D_8D31));
  cover property (@cb disable iff (!reset_n)
                  (readdata == 32'h0000_00FF) ##1 (readdata == 32'h590D_8D31));
  cover property (@cb disable iff (!reset_n)
                  (readdata == 32'h590D_8D31) ##1 (readdata == 32'h0000_00FF));
endmodule

bind soc_design_SystemID soc_design_SystemID_sva sva_inst (
  .clock(clock),
  .reset_n(reset_n),
  .address(address),
  .readdata(readdata)
);