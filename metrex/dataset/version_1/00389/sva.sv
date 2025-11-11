// SVA for bin2gray: functional correctness, robustness, and compact coverage

// Bindable SVA module: golden gray computation, inverse check, X-prop, coverage
module bin2gray_sva #(parameter int WIDTH = 4)
(
  input  logic [WIDTH-1:0] bin,
  input  logic [WIDTH-1:0] gray
);

  // Golden Gray encoding: g[MSB]=b[MSB], g[i]=b[i+1]^b[i]
  logic [WIDTH-1:0] gold_gray;
  assign gold_gray[WIDTH-1] = bin[WIDTH-1];
  genvar k;
  generate
    for (k = 0; k < WIDTH-1; k++) begin : gen_gold
      assign gold_gray[k] = bin[k+1] ^ bin[k];
    end
  endgenerate

  // Inverse (Gray -> Binary) helper
  function automatic logic [WIDTH-1:0] gray2bin(input logic [WIDTH-1:0] g);
    logic [WIDTH-1:0] b;
    b[WIDTH-1] = g[WIDTH-1];
    for (int i = WIDTH-2; i >= 0; i--) b[i] = b[i+1] ^ g[i];
    return b;
  endfunction

  // Functional correctness against golden model
  a_gray_correct: assert property (@(*) gray == gold_gray);

  // Round-trip consistency (detects many classes of bugs)
  a_roundtrip:    assert property (@(*) bin == gray2bin(gray));

  // Clean-inputs imply clean-outputs (no X/Z propagation)
  a_no_x:         assert property (@(*) (!$isunknown(bin)) |-> (!$isunknown(gray)));

  // Compact functional coverage: all input and output values observed
  genvar vi;
  generate
    for (vi = 0; vi < (1<<WIDTH); vi++) begin : cov_in_vals
      c_bin_vals:  cover property (@(*) bin  == vi[WIDTH-1:0]);
    end
  endgenerate

  genvar vo;
  generate
    for (vo = 0; vo < (1<<WIDTH); vo++) begin : cov_out_vals
      c_gray_vals: cover property (@(*) gray == vo[WIDTH-1:0]);
    end
  endgenerate

  // Bit-level checks (useful for quick pinpointing when failing)
  a_g3: assert property (@(*) gray[3] == bin[3]);
  a_g2: assert property (@(*) gray[2] == (bin[3]^bin[2]));
  a_g1: assert property (@(*) gray[1] == (bin[2]^bin[1]));
  a_g0: assert property (@(*) gray[0] == (bin[1]^bin[0]));

endmodule

// Optional: check internal wires as sanity (since they exist in the DUT)
module bin2gray_int_sva(
  input logic [3:0] bin,
  input logic       w1, w2, w3
);
  a_w1_def: assert property (@(*) w1 == (bin[0]^bin[1]));
  a_w2_def: assert property (@(*) w2 == (bin[1]^bin[2]));
  a_w3_def: assert property (@(*) w3 == (bin[2]^bin[3]));
endmodule

// Bind SVA to the DUT
bind bin2gray bin2gray_sva      #(.WIDTH(4)) u_bin2gray_sva(.bin(bin), .gray(gray));
bind bin2gray bin2gray_int_sva                          u_bin2gray_int_sva(.bin(bin), .w1(w1), .w2(w2), .w3(w3));