// SVA checker for temp_calculation
module temp_calculation_sva (
  input logic              clk,
  input logic              rst_n,
  input logic [2:0]        state,
  input logic [11:0]       value,
  input logic [4:0]        index,
  input logic [31:0]       temp
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional correctness
  assert property ( (state inside {3'd1,3'd2}) |-> (temp == 32'h0800_0001) );
  assert property ( !(state inside {3'd1,3'd2}) |-> (temp == {12'h03F, value, 8'h00}) );

  // No X/Z on output when inputs are known
  assert property ( (!$isunknown(state) && !$isunknown(value)) |-> !$isunknown(temp) );

  // Determinism and index independence
  assert property ( $stable(state) && $stable(value) |-> $stable(temp) );
  assert property ( $changed(index) && $stable(state) && $stable(value) |-> $stable(temp) );

  // Useful covers
  cover property ( state==3'd1 && temp==32'h0800_0001 );
  cover property ( state==3'd2 && temp==32'h0800_0001 );
  cover property ( !(state inside {3'd1,3'd2}) && temp=={12'h03F, value, 8'h00} );
  cover property ( !(state inside {3'd1,3'd2}) && value==12'h000 );
  cover property ( !(state inside {3'd1,3'd2}) && value==12'hFFF );
  cover property ( $changed(index) && $stable(state) && $stable(value) );
  cover property ( state==3'd1 ##1 state==3'd2 );
  cover property ( state==3'd2 ##1 !(state inside {3'd1,3'd2}) );
  cover property ( !(state inside {3'd1,3'd2}) ##1 state==3'd1 );
endmodule

// Bind example (connect clk/rst_n from your environment)
bind temp_calculation temp_calculation_sva sva_i(
  .clk(clk), .rst_n(rst_n),
  .state(state), .value(value), .index(index), .temp(temp)
);