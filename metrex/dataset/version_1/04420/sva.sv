// SVA for Bit_Shifting (bindable). Concise, checks functionality and key corner cases.
module Bit_Shifting_sva #(
  parameter int n = 8,
  parameter int log2n = 3
)(
  input logic                       clk,
  input logic        [n-1:0]        data_in,
  input logic        [log2n-1:0]    shift_amt,
  input logic        [1:0]          shift_type,
  input logic        [n-1:0]        data_out
);

  default clocking @(posedge clk); endclocking

  // Static parameter sanity
  initial begin
    if ((1 << log2n) < n) $error("Bit_Shifting: log2n (%0d) too small for n (%0d)", log2n, n);
  end

  // Controls must be known (avoid X/Z on control path)
  a_no_x_ctrl: assert property (!$isunknown({shift_type, shift_amt}))
    else $error("Bit_Shifting: X/Z on control inputs");

  // If all inputs known, output must be known
  a_no_x_out: assert property ( (!$isunknown({data_in, shift_amt, shift_type})) |-> !$isunknown(data_out) )
    else $error("Bit_Shifting: X/Z propagated to data_out with known inputs");

  // Golden functional specification (also flags unsigned >>> misuse if present)
  a_functional: assert property (
    data_out ==
      ((shift_type==2'b00) ? (data_in <<  shift_amt) :
       (shift_type==2'b01) ? ($signed(data_in) >>> shift_amt) :
       (shift_type==2'b10) ? (data_in >>  shift_amt) :
                             data_in)
  ) else $error("Bit_Shifting: functional mismatch");

  // Shift-by-zero must be passthrough for all modes
  a_shift0_passthru: assert property (shift_amt==0 |-> data_out==data_in)
    else $error("Bit_Shifting: shift_amt==0 not passthrough");

  // Minimal coverage: exercise each mode and key counts, including sign-extend case
  c_lls_0:    cover property (shift_type==2'b00 && shift_amt==0);
  c_lls_max:  cover property (shift_type==2'b00 && shift_amt==n-1);
  c_lrs_1:    cover property (shift_type==2'b10 && shift_amt==1);
  c_lrs_max:  cover property (shift_type==2'b10 && shift_amt==n-1);
  c_ars_pos:  cover property (shift_type==2'b01 && data_in[n-1]==1'b0 && shift_amt==1);
  c_ars_neg:  cover property (shift_type==2'b01 && data_in[n-1]==1'b1 && shift_amt==1);
  c_default:  cover property (shift_type==2'b11);

endmodule

// Example bind (replace tb_clk with your clock)
// bind Bit_Shifting Bit_Shifting_sva #(.n(n), .log2n(log2n))
//   u_bit_shifting_sva ( .clk(tb_clk), .data_in(data_in), .shift_amt(shift_amt),
//                        .shift_type(shift_type), .data_out(data_out) );