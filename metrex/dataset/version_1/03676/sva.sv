// SVA for seven_seg
// Bind this file to the DUT: bind seven_seg seven_seg_sva sva_i (.*);

module seven_seg_sva (
  input  wire        clk, clr,
  input  wire [1:0]  Scanning,
  input  wire [1:0]  SW,
  input  wire [31:0] disp_num,
  input  wire [3:0]  AN,
  input  wire [7:0]  SEGMENT,

  // internal DUT signals (connected via bind .*)
  input  wire [3:0]  digit,
  input  wire [7:0]  temp_seg,
  input  wire [7:0]  digit_seg,
  input  wire [15:0] disp_current
);

  default clocking cb @(posedge clk); endclocking

  function automatic [7:0] lut(input logic [3:0] d);
    case (d)
      4'h0: lut = 8'b10000001;
      4'h1: lut = 8'b11001111;
      4'h2: lut = 8'b10010010;
      4'h3: lut = 8'b10000110;
      4'h4: lut = 8'b11001100;
      4'h5: lut = 8'b10100100;
      4'h6: lut = 8'b10100000;
      4'h7: lut = 8'b10001111;
      4'h8: lut = 8'b10000000;
      4'h9: lut = 8'b10000100;
      4'hA: lut = 8'b10001000;
      4'hB: lut = 8'b11100000;
      4'hC: lut = 8'b10110001;
      4'hD: lut = 8'b11000010;
      4'hE: lut = 8'b10110000;
      4'hF: lut = 8'b10111000;
      default: lut = 8'b00000000;
    endcase
  endfunction

  // Basic muxing and range checks
  a_disp_current_mux: assert property (disp_current == (SW[1] ? disp_num[31:16] : disp_num[15:0]));
  a_segment_mux:      assert property (SEGMENT      == (SW[0] ? digit_seg           : temp_seg));

  // AN correctness and one-hot-low
  a_an_by_scan: assert property (
    AN == (Scanning==2'd0 ? 4'b1110 :
           Scanning==2'd1 ? 4'b1101 :
           Scanning==2'd2 ? 4'b1011 :
                             4'b0111)
  );
  a_an_onehot_low: assert property ($onehot(~AN));

  // temp_seg mapping per scan slot
  a_temp_seg_s0: assert property (Scanning==2'd0 |-> temp_seg == {disp_num[24], disp_num[ 0], disp_num[ 4], disp_num[16],
                                                                   disp_num[25], disp_num[17], disp_num[ 5], disp_num[12]});
  a_temp_seg_s1: assert property (Scanning==2'd1 |-> temp_seg == {disp_num[26], disp_num[ 1], disp_num[ 6], disp_num[18],
                                                                   disp_num[27], disp_num[19], disp_num[ 7], disp_num[13]});
  a_temp_seg_s2: assert property (Scanning==2'd2 |-> temp_seg == {disp_num[28], disp_num[ 2], disp_num[ 8], disp_num[20],
                                                                   disp_num[29], disp_num[21], disp_num[ 9], disp_num[14]});
  a_temp_seg_s3: assert property (Scanning==2'd3 |-> temp_seg == {disp_num[30], disp_num[ 3], disp_num[10], disp_num[22],
                                                                   disp_num[31], disp_num[23], disp_num[11], disp_num[15]});

  // digit load per scan slot (from disp_current)
  a_digit_s0: assert property (Scanning==2'd0 |-> digit == disp_current[ 3: 0]);
  a_digit_s1: assert property (Scanning==2'd1 |-> digit == disp_current[ 7: 4]);
  a_digit_s2: assert property (Scanning==2'd2 |-> digit == disp_current[11: 8]);
  a_digit_s3: assert property (Scanning==2'd3 |-> digit == disp_current[15:12]);

  // digit_seg follows LUT of prior-cycle digit (separate always blocks => next-cycle relation)
  a_digitseg_lut_next: assert property (digit_seg == lut($past(digit)));

  // Knownness
  a_no_x_outputs: assert property (!$isunknown({AN, SEGMENT}));
  a_no_x_internals: assert property (!$isunknown({digit, temp_seg, digit_seg}));

  // Minimal functional coverage
  cover_sw0_0: cover property (SW[0]==1'b0);
  cover_sw0_1: cover property (SW[0]==1'b1);
  cover_sw1_0: cover property (SW[1]==1'b0);
  cover_sw1_1: cover property (SW[1]==1'b1);

  cover_scan0: cover property (Scanning==2'd0);
  cover_scan1: cover property (Scanning==2'd1);
  cover_scan2: cover property (Scanning==2'd2);
  cover_scan3: cover property (Scanning==2'd3);

  // Cover all digit values seen
  genvar i;
  generate
    for (i=0;i<16;i++) begin : COV_DIG
      cover property (digit == i[3:0]);
    end
  endgenerate

endmodule

// Bind to DUT
bind seven_seg seven_seg_sva sva_i (.*);