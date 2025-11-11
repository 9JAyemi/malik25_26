// SVA for square_wave_gen
module square_wave_gen_sva (
  input  logic        clk,
  input  logic        freq,
  input  logic        square_wave,
  input  logic [31:0] counter,
  input  logic [31:0] half_period,
  input  logic [31:0] clk_period
);

  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate || $isunknown({freq, square_wave, counter, half_period, clk_period}));

  // Safety: no divide-by-zero on clk_period update
  assert property (freq != 1'b0);

  // Counter behavior
  assert property ((counter != half_period) |=> counter == $past(counter) + 32'd1);
  assert property ((counter == half_period) |=> counter == 32'd0);

  // Output behavior (toggle iff compare hit)
  assert property ((counter == half_period) |=> square_wave != $past(square_wave));
  assert property ((counter != half_period) |=> square_wave == $past(square_wave));
  assert property ((square_wave != $past(square_wave)) |-> $past(counter == half_period));

  // half_period update (uses previous clk_period)
  assert property (half_period == $past(clk_period) / 32'd2);

  // clk_period update (uses previous values; guard division)
  assert property ($past(freq) != 1'b0 |-> clk_period ==
                   ((($past(clk_period)/$past(freq)) != 0) ? ($past(clk_period)/$past(freq)) : 32'd0));

  // Basic coverage
  cover property (counter == half_period);
  cover property (square_wave != $past(square_wave));                // any toggle
  cover property ($rose(square_wave));                                // rising edge seen
  cover property ($fell(square_wave));                                // falling edge seen

endmodule

bind square_wave_gen square_wave_gen_sva sva_i (.*);