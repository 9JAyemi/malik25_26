// SVA for pipeline_register
module pipeline_register_sva (
  input  logic        CLK,
  input  logic        EN,
  input  logic [31:0] DATA_IN,
  input  logic [31:0] DATA_OUT_1,
  input  logic [31:0] DATA_OUT_2,
  input  logic [31:0] DATA_OUT_3
);
  default clocking cb @(posedge CLK); endclocking

  // past-valid guards for $past depth 1/2/3
  logic pv1, pv2, pv3;
  always @(cb) begin
    pv1 <= 1'b1;
    pv2 <= pv1;
    pv3 <= pv2;
  end

  // Combinational pass-through
  a_passthrough: assert property (DATA_OUT_3 == DATA_IN);

  // Hold behavior when disabled
  a_hold:        assert property (!EN |-> $stable(DATA_OUT_1) && $stable(DATA_OUT_2));

  // One-step shift within the pipeline when enabled
  a_shift_o2_o1: assert property (pv1 && EN |-> DATA_OUT_2 == $past(DATA_OUT_1));

  // Latency to DATA_IN under consecutive enables
  a_o1_din_1:    assert property (pv2 && EN && $past(EN) |-> DATA_OUT_1 == $past(DATA_IN));
  a_o2_din_2:    assert property (pv3 && EN && $past(EN) && $past(EN,2) |-> DATA_OUT_2 == $past(DATA_IN,2));

  // Basic covers: hold, single/continuous shifts, end-to-end movement
  c_hold3:       cover  property (!EN[*3]);
  c_burst3:      cover  property (pv3 && EN && $past(EN) && $past(EN,2));
  c_o1_flow:     cover  property (pv2 && EN && $past(EN) && DATA_OUT_1 == $past(DATA_IN));
  c_o2_flow:     cover  property (pv3 && EN && $past(EN) && $past(EN,2) && DATA_OUT_2 == $past(DATA_IN,2));
endmodule

bind pipeline_register pipeline_register_sva sva_i (.*);