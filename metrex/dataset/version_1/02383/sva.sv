// SVA for square_wave_generator
module square_wave_generator_sva #(parameter int unsigned TC = 499_999) (
  input  logic        clk,
  input  logic [31:0] counter,
  input  logic        square_wave
);
  default clocking cb @(posedge clk); endclocking

  // Counter next-state behavior
  assert property (
    !$isunknown(counter) && !$isunknown($past(counter))
    |-> ( ($past(counter)==TC) ? (counter==32'd0)
                               : (counter==$past(counter)+32'd1) )
  );

  // Square-wave toggles iff wrap occurs
  assert property (
    !$isunknown($past(counter)) && !$isunknown(square_wave) && !$isunknown($past(square_wave))
    |-> ( ($past(counter)==TC) ? (square_wave != $past(square_wave))
                               : (square_wave == $past(square_wave)) )
  );

  // Once counter is in-range, it stays in-range
  assert property (
    !$isunknown(counter) && !$isunknown($past(counter)) && ($past(counter) inside {[32'd0:TC]})
    |-> (counter inside {[32'd0:TC]})
  );

  // Exact spacing: stable for TC cycles, then toggle on the next cycle
  assert property (
    !$isunknown(square_wave) && !$isunknown($past(square_wave)) && (square_wave != $past(square_wave))
    |-> ( (square_wave == $past(square_wave))[*TC] ##1 (square_wave != $past(square_wave)) )
  );

  // Coverage
  cover property (
    !$isunknown(counter) && !$isunknown($past(counter)) &&
    !$isunknown(square_wave) && !$isunknown($past(square_wave)) &&
    ($past(counter)==TC && counter==0 && square_wave != $past(square_wave))
  );

  cover property (
    !$isunknown(square_wave) && !$isunknown($past(square_wave)) &&
    (square_wave != $past(square_wave)) ##(TC+1) (square_wave != $past(square_wave))
  );
endmodule

// Bind into DUT (access internal counter)
bind square_wave_generator square_wave_generator_sva #(.TC(499_999))
  i_square_wave_generator_sva (.clk(clk), .counter(counter), .square_wave(square_wave));