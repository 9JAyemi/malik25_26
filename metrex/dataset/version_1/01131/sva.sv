// SystemVerilog Assertions for top_module and submodules (concise, quality-focused)

`ifndef TOP_SVA
`define TOP_SVA

// -------------------- Barrel Shifter SVA --------------------
module barrel_shifter_sva (
  input logic                 clk,
  input logic                 reset,
  input logic [1:0]           shift_sel,
  input logic [2:0]           shift_amt,
  input logic [7:0]           shift_reg,
  input logic [3:0]           shift_out
);
  default clocking cb @(posedge clk); endclocking

  function automatic [7:0] f_next_sr(input [7:0] sr, input [1:0] sel);
    case (sel)
      2'b00: f_next_sr = sr;
      2'b01: f_next_sr = {sr[6:0], 1'b0};
      2'b10: f_next_sr = {1'b0, sr[7:1]};
      default: f_next_sr = {2'b00, sr[7:2]};
    endcase
  endfunction

  function automatic [3:0] f_slice4(input [7:0] sr, input [2:0] amt);
    case (amt)
      3'b000: f_slice4 = sr[3:0];
      3'b001: f_slice4 = sr[4:1];
      3'b010: f_slice4 = sr[5:2];
      3'b011: f_slice4 = sr[6:3];
      default: f_slice4 = 4'bx;
    endcase
  endfunction

  // Reset effects
  ap_reset_clears_sr:       assert property (reset |=> shift_reg == 8'h00);
  ap_sr_zero_while_reset:   assert property (reset && $past(reset) |-> shift_reg == 8'h00);
  ap_out_stable_on_reset:   assert property (reset && $past(reset) |-> $stable(shift_out));

  // Sequential correctness
  ap_sr_update:             assert property (disable iff (reset)
                                   shift_reg == f_next_sr($past(shift_reg), $past(shift_sel)));
  ap_out_select:            assert property (disable iff (reset)
                                   shift_out == f_slice4($past(shift_reg), $past(shift_amt)));

  // X-behavior and validity
  ap_invalid_amt_x:         assert property (disable iff (reset)
                                   ($past(shift_amt) >= 3'b100) |-> $isunknown(shift_out));
  ap_valid_amt_no_x:        assert property (disable iff (reset)
                                   ($past(shift_amt) <= 3'b011 && !$isunknown($past(shift_reg)))
                                   |-> !$isunknown(shift_out));

  // Coverage
  genvar i;
  generate
    for (i=0;i<4;i++) begin : CSEL
      cp_shift_sel: cover property (disable iff (reset) $past(shift_sel)==i);
    end
    for (i=0;i<5;i++) begin : CAMT // cover 0..3 valid and one invalid (4)
      cp_shift_amt: cover property (disable iff (reset) $past(shift_amt)==i[2:0]);
    end
  endgenerate
endmodule

// -------------------- Top-level SVA (incl. decoder + OR) --------------------
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  data_in,
  input  logic [2:0]  sel,
  input  logic [3:0]  q,
  input  logic [3:0]  q_shifted,
  input  logic [3:0]  q_decoded
);
  default clocking cb @(posedge clk); endclocking

  // Bitwise OR correctness
  ap_or_correct: assert property (q == (q_shifted | q_decoded));

  // Decoder functional equivalence
  function automatic [3:0] f_decode(input logic [7:0] din, input logic en);
    if (en) begin
      case (din[7:6])
        2'b00: f_decode = 4'b0000;
        2'b01: f_decode = 4'b0001;
        2'b10: f_decode = 4'b0010;
        default: f_decode = 4'b0011;
      endcase
    end else begin
      case (din[5:4])
        2'b00: f_decode = 4'b0100;
        2'b01: f_decode = 4'b0101;
        2'b10: f_decode = 4'b0110;
        default: f_decode = 4'b0111;
      endcase
    end
  endfunction

  ap_decoder_eq:  assert property (q_decoded == f_decode(data_in, sel[2]));
  ap_decoder_no_x:assert property ((!$isunknown({data_in, sel[2]})) |-> !$isunknown(q_decoded));

  // Optional: flag illegal shift amounts seen by system (sel==4..7)
  ap_no_illegal_sel: cover property (disable iff (reset) sel >= 3'd4); // covered if exercised

  // Coverage: exercise all sel values and decoder outputs
  genvar j;
  generate
    for (j=0;j<8;j++) begin : CSEL_ALL
      cp_sel_vals: cover property (disable iff (reset) sel == j[2:0]);
    end
  endgenerate

  // decoder outputs 0000..0011 (en=1) and 0100..0111 (en=0)
  generate
    for (j=0;j<8;j++) begin : CDEC_ALL
      cp_dec_outs: cover property (q_decoded == j[3:0]);
    end
  endgenerate

  // Output integrity (no X when inputs known)
  ap_or_no_x: assert property ((!$isunknown({q_shifted,q_decoded})) |-> !$isunknown(q));
endmodule

// -------------------- Binds --------------------
bind barrel_shifter  barrel_shifter_sva bs_sva_i(
  .clk(clk), .reset(reset), .shift_sel(shift_sel), .shift_amt(shift_amt),
  .shift_reg(shift_reg), .shift_out(shift_out)
);

bind top_module top_module_sva top_sva_i(
  .clk(clk), .reset(reset), .data_in(data_in), .sel(sel),
  .q(q), .q_shifted(q_shifted), .q_decoded(q_decoded)
);

`endif