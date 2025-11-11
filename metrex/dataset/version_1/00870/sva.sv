// SVA checkers and binds for the provided design

// ------------------------
// square_wave_generator SVA
// ------------------------
module square_wave_generator_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        square_wave,
  input  logic [31:0] counter
);
  localparam logic [31:0] MAX = 32'd49999999;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Async reset drives known values immediately
  assert property (@(posedge reset) square_wave == 1'b0 && counter == 32'd0);

  // Counter range
  assert property (counter <= MAX);

  // Normal counting behavior (no wrap): increment by 1, square_wave stable
  assert property (counter != MAX |=> counter == $past(counter) + 1 && $stable(square_wave));

  // Wrap at MAX and toggle square_wave
  assert property (counter == MAX |=> counter == 32'd0 && square_wave == ~$past(square_wave));

  // square_wave toggles only at wrap
  assert property ($changed(square_wave) |-> $past(counter) == MAX);

  // No X/Z after reset deassertion
  assert property (!$isunknown({square_wave, counter}));  

  // Coverage
  cover property (counter == MAX ##1 counter == 32'd0 && $changed(square_wave));
  cover property (square_wave == 1'b0 ##1 square_wave == 1'b1);
endmodule

bind square_wave_generator square_wave_generator_sva swg_sva_i (
  .clk        (clk),
  .reset      (reset),
  .square_wave(square_wave),
  .counter    (counter)
);

// -------------
// adder SVA
// -------------
module adder_sva (
  input  logic [15:0] A,
  input  logic [15:0] B,
  input  logic        Cin,
  input  logic [15:0] S,
  input  logic        Cout
);
  // Functional correctness
  assert property ({Cout, S} == A + B + Cin);

  // No X/Z on outputs
  assert property (!$isunknown({S, Cout}));

  // Coverage on carry
  cover property (Cout == 1'b1);
  cover property (Cout == 1'b0);
endmodule

bind adder adder_sva adder_sva_i (
  .A   (A),
  .B   (B),
  .Cin (Cin),
  .S   (S),
  .Cout(Cout)
);

// -----------------
// final_module SVA
// -----------------
module final_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        square_wave,
  input  logic [15:0] A,
  input  logic [15:0] B,
  input  logic        Cin,
  input  logic [15:0] adder_output,
  input  logic [15:0] subtractor_output,
  input  logic [15:0] final_output
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Internal path equivalence checks
  assert property (subtractor_output == (A - B));
  assert property (adder_output == (A + B + Cin)[15:0]);

  // Final output functional correctness (modulo 16b arithmetic)
  assert property (
    final_output ==
      (square_wave
        ? (adder_output + subtractor_output)
        : (adder_output - subtractor_output))
  );

  // No X/Z on final output
  assert property (!$isunknown(final_output));

  // Cover both mux paths
  cover property (square_wave == 1'b0);
  cover property (square_wave == 1'b1);

  // Cover potential wrap on add/sub path
  cover property (square_wave && ({1'b0,adder_output} + {1'b0,subtractor_output})[16]);
  cover property (!square_wave && (adder_output < subtractor_output)); // borrow/wrap on subtraction path
endmodule

bind final_module final_module_sva fm_sva_i (
  .clk               (clk),
  .reset             (reset),
  .square_wave       (square_wave),
  .A                 (A),
  .B                 (B),
  .Cin               (Cin),
  .adder_output      (adder_output),
  .subtractor_output (subtractor_output),
  .final_output      (final_output)
);