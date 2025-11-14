// SVA for db_sao_cal_diff
module db_sao_cal_diff_sva
  #(parameter int W=288, SEG=9, SLOTS=32)
(
  input  logic [7:0]  dp_i,
  input  logic [7:0]  op_i,
  input  logic        data_valid_i,
  input  logic [W-1:0]      ominusdp_o,
  input  logic [SLOTS-1:0]  index_o
);

  localparam int SLOT_W = SEG;
  localparam int ZW     = W-SEG;

  function automatic logic signed [SEG-1:0] diff(input logic [7:0] op, input logic [7:0] dp);
    diff = $signed({1'b0,op}) - $signed({1'b0,dp});
  endfunction

  function automatic logic [W-1:0] slot(input logic signed [SEG-1:0] v, input logic [4:0] idx);
    slot = ({{ZW{1'b0}}, v} << (SEG*idx));
  endfunction

  function automatic logic [SLOTS-1:0] onehot(input logic [4:0] idx);
    onehot = (SLOTS'(1) << idx);
  endfunction

  wire logic [4:0] idx = dp_i[7:3];

  // Core functional equivalence and gating
  always @* begin
    assert (data_valid_i
            ? (ominusdp_o == W'(0) && index_o == SLOTS'(0))
            : (ominusdp_o == slot(diff(op_i,dp_i), idx) && index_o == onehot(idx)))
      else $error("db_sao_cal_diff mismatch");

    if (!data_valid_i) begin
      assert ($onehot(index_o)) else $error("index_o not onehot when valid");

      // Segment correctness: only selected 9-bit slot carries diff, others zero
      for (int s = 0; s < SLOTS; s++) begin
        if (s == idx)
          assert (ominusdp_o[SEG*s +: SEG] == diff(op_i,dp_i))
            else $error("payload segment incorrect");
        else
          assert (ominusdp_o[SEG*s +: SEG] == '0)
            else $error("non-selected segment non-zero");
      end
    end

    // No unknowns on outputs
    assert (!$isunknown(ominusdp_o) && !$isunknown(index_o))
      else $error("X/Z on outputs");
  end

  // Compact SVA coverage
  always @* begin
    // Hit all 32 index slots when valid
    for (int s = 0; s < SLOTS; s++) cover (!data_valid_i && idx == s);

    // Result sign bins
    cover (!data_valid_i && diff(op_i,dp_i) < 0);
    cover (!data_valid_i && diff(op_i,dp_i) == 0);
    cover (!data_valid_i && diff(op_i,dp_i) > 0);

    // Extremes
    cover (!data_valid_i && op_i==8'hFF && dp_i==8'h00); // +255
    cover (!data_valid_i && op_i==8'h00 && dp_i==8'hFF); // -255
  end

endmodule

// Bind into DUT
bind db_sao_cal_diff db_sao_cal_diff_sva sva_db_sao_cal_diff (
  .dp_i(dp_i),
  .op_i(op_i),
  .data_valid_i(data_valid_i),
  .ominusdp_o(ominusdp_o),
  .index_o(index_o)
);