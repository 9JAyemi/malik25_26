// SVA for bmu: checks truth table, X/range, and provides coverage.
// Bind this file to the DUT.

module bmu_sva (
  input  logic       cx0, cx1,
  input  logic [1:0] bm0, bm1, bm2, bm3, bm4, bm5, bm6, bm7
);

  // Trigger assertions on any input edge; use ##0 to observe post-NBA outputs.
  default clocking cb @(posedge cx0 or negedge cx0 or posedge cx1 or negedge cx1); endclocking

  // Expected output vectors (bm0..bm7) for each input combination
  localparam logic [15:0] V00 = {2'd0,2'd2,2'd2,2'd0,2'd1,2'd1,2'd1,2'd1};
  localparam logic [15:0] V01 = {2'd1,2'd1,2'd1,2'd1,2'd2,2'd0,2'd0,2'd2};
  localparam logic [15:0] V10 = {2'd1,2'd1,2'd1,2'd1,2'd0,2'd2,2'd2,2'd0};
  localparam logic [15:0] V11 = {2'd2,2'd0,2'd0,2'd2,2'd1,2'd1,2'd1,2'd1};

  // No unknowns on inputs
  assert property ( !$isunknown({cx0,cx1}) ) else $error("bmu: X/Z on inputs");

  // Outputs are never X/Z after input change
  assert property ( 1 |-> ##0 !$isunknown({bm0,bm1,bm2,bm3,bm4,bm5,bm6,bm7}) )
    else $error("bmu: X/Z on outputs after input change");

  // Outputs limited to 0/1/2 after input change
  assert property ( 1 |-> ##0
                    (bm0 inside {2'd0,2'd1,2'd2}) && (bm1 inside {2'd0,2'd1,2'd2}) &&
                    (bm2 inside {2'd0,2'd1,2'd2}) && (bm3 inside {2'd0,2'd1,2'd2}) &&
                    (bm4 inside {2'd0,2'd1,2'd2}) && (bm5 inside {2'd0,2'd1,2'd2}) &&
                    (bm6 inside {2'd0,2'd1,2'd2}) && (bm7 inside {2'd0,2'd1,2'd2}) )
    else $error("bmu: output out of allowed range {0,1,2}");

  // Truth table checks (evaluate outputs after NBA with ##0)
  assert property ( ({cx0,cx1}==2'b00) |-> ##0 ({bm0,bm1,bm2,bm3,bm4,bm5,bm6,bm7}==V00) )
    else $error("bmu: mapping mismatch for cx={0,0}");
  assert property ( ({cx0,cx1}==2'b01) |-> ##0 ({bm0,bm1,bm2,bm3,bm4,bm5,bm6,bm7}==V01) )
    else $error("bmu: mapping mismatch for cx={0,1}");
  assert property ( ({cx0,cx1}==2'b10) |-> ##0 ({bm0,bm1,bm2,bm3,bm4,bm5,bm6,bm7}==V10) )
    else $error("bmu: mapping mismatch for cx={1,0}");
  assert property ( ({cx0,cx1}==2'b11) |-> ##0 ({bm0,bm1,bm2,bm3,bm4,bm5,bm6,bm7}==V11) )
    else $error("bmu: mapping mismatch for cx={1,1}");

  // Coverage: hit all input combos and their corresponding outputs
  cover property ( ({cx0,cx1}==2'b00) ##0 ({bm0,bm1,bm2,bm3,bm4,bm5,bm6,bm7}==V00) );
  cover property ( ({cx0,cx1}==2'b01) ##0 ({bm0,bm1,bm2,bm3,bm4,bm5,bm6,bm7}==V01) );
  cover property ( ({cx0,cx1}==2'b10) ##0 ({bm0,bm1,bm2,bm3,bm4,bm5,bm6,bm7}==V10) );
  cover property ( ({cx0,cx1}==2'b11) ##0 ({bm0,bm1,bm2,bm3,bm4,bm5,bm6,bm7}==V11) );

endmodule

bind bmu bmu_sva u_bmu_sva (
  .cx0(cx0), .cx1(cx1),
  .bm0(bm0), .bm1(bm1), .bm2(bm2), .bm3(bm3),
  .bm4(bm4), .bm5(bm5), .bm6(bm6), .bm7(bm7)
);