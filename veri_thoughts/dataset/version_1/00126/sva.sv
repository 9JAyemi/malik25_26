// SVA for clock_gate — concise, high-quality checks and coverage

module clock_gate_sva (
  input logic clk,
  input logic en,
  input logic te,
  input logic enclk
);
  default clocking cb @(posedge clk); endclocking

  // Functional spec per Verilog if semantics
  assert property ( (en === 1'b1 && te === 1'b1) |-> (enclk == 1'b1) );
  assert property ( (en !== 1'b1 || te !== 1'b1) |-> (enclk == 1'b0) );

  // Output must be known on every clock
  assert property ( !$isunknown(enclk) );

  // No glitches: enclk can only change on clk posedge
  assert property (@(posedge enclk) $rose(clk));
  assert property (@(negedge enclk) $rose(clk));

  // Truth-table coverage at clock edge
  cover property ( en===1'b0 && te===1'b0 && enclk==1'b0 );
  cover property ( en===1'b0 && te===1'b1 && enclk==1'b0 );
  cover property ( en===1'b1 && te===1'b0 && enclk==1'b0 );
  cover property ( en===1'b1 && te===1'b1 && enclk==1'b1 );

  // Toggle coverage
  cover property (@(posedge enclk) 1);
  cover property (@(negedge enclk) 1);
endmodule

bind clock_gate clock_gate_sva u_clock_gate_sva (.clk(clk), .en(en), .te(te), .enclk(enclk));