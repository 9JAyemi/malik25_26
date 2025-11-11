// SVA for dc_offset_removal and its submodules.
// Concise, high‑value checks with key coverage.
// Bind these modules into your DUT after compilation.

////////////////////////////////////////////////////////////
// dc_offset_removal SVA
////////////////////////////////////////////////////////////
module dc_offset_removal_sva
  #(parameter int WIDTH=16,
    parameter logic [7:0] ADDR=8'd0,
    parameter int alpha_shift=20,
    parameter int int_width = WIDTH + alpha_shift)
(
  input  logic                  clk,
  input  logic                  rst,
  input  logic                  set_stb,
  input  logic [7:0]            set_addr,
  input  logic [31:0]           set_data,
  input  logic [WIDTH-1:0]      in,
  input  logic [WIDTH-1:0]      out,

  // internal taps
  input  logic                  set_now,
  input  logic                  fixed,
  input  logic [int_width-1:0]  integrator,
  input  logic [WIDTH-1:0]      quantized
);

  // Elaboration-time sanity
  initial begin
    assert (alpha_shift >= 1)
      else $error("alpha_shift must be >= 1 for round_sd to be well-defined");
    assert (int_width == WIDTH + alpha_shift)
      else $error("int_width param mismatch");
  end

  // Helpers
  localparam signed [WIDTH:0]  LIM_POS_P1 = (1'sd1 <<< (WIDTH-1)); // +2^(W-1)
  localparam signed [WIDTH-1:0] MAX_S     = LIM_POS_P1 - 1;        //  2^(W-1)-1
  localparam signed [WIDTH-1:0] MIN_S     = -LIM_POS_P1;           // -2^(W-1)

  function automatic signed [int_width-1:0] sext_in(input logic [WIDTH-1:0] x);
    return { {alpha_shift{x[WIDTH-1]}}, x };
  endfunction

  function automatic signed [WIDTH-1:0] satW(input signed [WIDTH:0] x);
    if (x > MAX_S) return MAX_S;
    else if (x < MIN_S) return MIN_S;
    else return x[WIDTH-1:0];
  endfunction

  // set_now definition
  assert property (@(posedge clk) set_now == (set_stb && (ADDR == set_addr)));

  // Reset behavior (next cycle observed)
  assert property (@(posedge clk) rst |=> (fixed == 1'b0 && integrator == '0));

  // fixed only changes on rst or set_now
  assert property (@(posedge clk)
                   $changed(fixed) |-> ($past(rst) || $past(set_now)));

  // When set_now, fixed is loaded from set_data[31] next cycle
  assert property (@(posedge clk) disable iff (rst)
                   set_now |=> fixed == $past(set_data[31]));

  // When set_now and set_data[30]==1, integrator loads literal next cycle
  assert property (@(posedge clk) disable iff (rst)
                   (set_now && set_data[30]) |=> integrator
                     == { $past(set_data[29:0]), {(int_width-30){1'b0}} });

  // When set_now and set_data[30]==0, integrator holds (no accumulation that cycle)
  assert property (@(posedge clk) disable iff (rst)
                   (set_now && !set_data[30]) |=> $stable(integrator));

  // Normal accumulation when not fixed and not set_now
  assert property (@(posedge clk) disable iff (rst)
                   (!set_now && !fixed) |=> integrator
                     == $past(integrator) + sext_in($past(in)));

  // Hold integrator when fixed and not set_now
  assert property (@(posedge clk) disable iff (rst)
                   (!set_now && fixed) |=> $stable(integrator));

  // Output equals saturated (in - quantized) next cycle
  assert property (@(posedge clk) disable iff (rst)
                   1'b1 |=> $signed(out) == satW($signed($past(in)) - $signed($past(quantized))));

  // Out always within signed range
  assert property (@(posedge clk) ($signed(out) <= MAX_S) && ($signed(out) >= MIN_S));

  // Coverage: set sequences, accumulation, and output rails
  cover property (@(posedge clk) disable iff (rst)
                  set_now ##1 fixed);

  cover property (@(posedge clk) disable iff (rst)
                  (!set_now && !fixed) ##1 (!set_now && !fixed));

  cover property (@(posedge clk) $rose(fixed));
  cover property (@(posedge clk) $fell(fixed));

  cover property (@(posedge clk) $signed(out) == MAX_S);
  cover property (@(posedge clk) $signed(out) == MIN_S);

endmodule

bind dc_offset_removal dc_offset_removal_sva
  #(.WIDTH(WIDTH), .ADDR(ADDR), .alpha_shift(alpha_shift))
  dc_offset_removal_sva_i
  ( .clk(clk), .rst(rst), .set_stb(set_stb), .set_addr(set_addr), .set_data(set_data),
    .in(in), .out(out),
    .set_now(set_now), .fixed(fixed), .integrator(integrator), .quantized(quantized) );


////////////////////////////////////////////////////////////
// round_sd SVA
////////////////////////////////////////////////////////////
module round_sd_sva
  #(parameter int WIDTH_IN=16, WIDTH_OUT=16,
    parameter int WIDTH_OUT_1 = WIDTH_OUT - 1,
    parameter int WIDTH_IN_1  = WIDTH_IN - 1,
    parameter int WIDTH_DIFF  = WIDTH_IN - WIDTH_OUT,
    parameter int WIDTH_DIFF_1 = WIDTH_DIFF - 1,
    parameter int ROUND_CONST = (1 << (WIDTH_DIFF - 1)) - 1)
(
  input  logic                          clk,
  input  logic                          reset,
  input  logic signed [WIDTH_IN-1:0]    in,
  input  logic                          strobe_in,
  input  logic signed [WIDTH_OUT-1:0]   out,
  input  logic                          strobe_out,

  // internal taps
  input  logic signed [WIDTH_IN_1:0]    in_shifted,
  input  logic signed [WIDTH_OUT_1:0]   out_shifted,
  input  logic [WIDTH_DIFF_1:0]         round_bits
);

  // Sanity
  initial begin
    assert (WIDTH_IN > WIDTH_OUT)
      else $error("round_sd: WIDTH_IN must be > WIDTH_OUT");
    assert (WIDTH_DIFF >= 1)
      else $error("round_sd: WIDTH_DIFF must be >= 1");
  end

  // Strobes align one-cycle (due to sequential reg behavior visibility)
  assert property (@(posedge clk) strobe_in |=> strobe_out);
  assert property (@(posedge clk) !strobe_in |=> !strobe_out);

  // Reset initializes regs (observe next cycle)
  assert property (@(posedge clk) reset |=> (out == '0 && strobe_out == 1'b0));

  // Shifter/round state updates on strobe_in
  assert property (@(posedge clk) disable iff (reset)
                   strobe_in |=> in_shifted == ($signed($past(in)) >> WIDTH_DIFF));

  assert property (@(posedge clk) disable iff (reset)
                   strobe_in |=> round_bits == (ROUND_CONST & $past(in[WIDTH_DIFF_1:0])));

  // Saturation stage degenerates to pass-through of prior out_shifted
  // (given out_shifted is already WIDTH_OUT wide)
  assert property (@(posedge clk) disable iff (reset)
                   1'b1 |=> out == $past(out_shifted));

  // Range always within signed limits by construction
  localparam signed [WIDTH_OUT-1:0] MAX_SO = (1'sd1 <<< (WIDTH_OUT-1)) - 1;
  localparam signed [WIDTH_OUT-1:0] MIN_SO = -(1'sd1 <<< (WIDTH_OUT-1));
  assert property (@(posedge clk)
                   ($signed(out) <= MAX_SO) && ($signed(out) >= MIN_SO));

  // Coverage: exercise nonzero rounding bits and both strobe states
  cover property (@(posedge clk) strobe_in ##1 strobe_out);
  cover property (@(posedge clk) !strobe_in ##1 !strobe_out);
  cover property (@(posedge clk) disable iff (reset)
                  strobe_in && (|$past(in[WIDTH_DIFF_1:0])));

endmodule

bind round_sd round_sd_sva
  #(.WIDTH_IN(WIDTH_IN), .WIDTH_OUT(WIDTH_OUT))
  round_sd_sva_i
  ( .clk(clk), .reset(reset), .in(in), .strobe_in(strobe_in), .out(out), .strobe_out(strobe_out),
    .in_shifted(in_shifted), .out_shifted(out_shifted), .round_bits(round_bits) );


////////////////////////////////////////////////////////////
// add2_and_clip_reg SVA
////////////////////////////////////////////////////////////
module add2_and_clip_reg_sva
  #(parameter int WIDTH=16)
(
  input  logic                       clk,
  input  logic                       rst,
  input  logic signed [WIDTH-1:0]    in1,
  input  logic signed [WIDTH-1:0]    in2,
  input  logic                       strobe_in,
  input  logic signed [WIDTH-1:0]    sum,
  input  logic                       strobe_out
);

  localparam signed [WIDTH:0]  LIM_POS_P1 = (1'sd1 <<< (WIDTH-1));
  localparam signed [WIDTH-1:0] MAX_S     = LIM_POS_P1 - 1;
  localparam signed [WIDTH-1:0] MIN_S     = -LIM_POS_P1;

  function automatic signed [WIDTH-1:0] satW(input signed [WIDTH:0] x);
    if (x > MAX_S) return MAX_S;
    else if (x < MIN_S) return MIN_S;
    else return x[WIDTH-1:0];
  endfunction

  // Reset behavior (next cycle)
  assert property (@(posedge clk) rst |=> (sum == '0 && strobe_out == 1'b0));

  // Strobe mirrors one-cycle (observed due to reg update visibility)
  assert property (@(posedge clk) strobe_in |=> strobe_out);
  assert property (@(posedge clk) !strobe_in |=> !strobe_out);

  // Functional spec: next-cycle sum equals saturated (in1+in2)
  assert property (@(posedge clk) disable iff (rst)
                   strobe_in |=> $signed(sum) == satW($signed($past(in1)) + $signed($past(in2))));

  // Range guard
  assert property (@(posedge clk) ($signed(sum) <= MAX_S) && ($signed(sum) >= MIN_S));

  // Coverage: hit positive and negative saturation
  cover property (@(posedge clk) $signed(sum) == MAX_S);
  cover property (@(posedge clk) $signed(sum) == MIN_S);

endmodule

bind add2_and_clip_reg add2_and_clip_reg_sva
  #(.WIDTH(WIDTH))
  add2_and_clip_reg_sva_i
  ( .clk(clk), .rst(rst), .in1(in1), .in2(in2), .strobe_in(strobe_in), .sum(sum), .strobe_out(strobe_out) );