// SVA checker for temperature_sensor
// Bind or instantiate this in your environment; provide a sampling clock.

checker temperature_sensor_sva (
  input logic        clk,
  input logic [9:0]  analog_in,
  input logic [3:0]  temp_range
);
  default clocking cb @ (posedge clk); endclocking

  // Golden mapping
  function automatic logic [3:0] exp_tr (input logic [9:0] a);
    if      (a == 10'd0)                 exp_tr = 4'b0000;
    else if (a inside {[10'd1:10'd9]})   exp_tr = 4'b0001;
    else if (a inside {[10'd10:10'd19]}) exp_tr = 4'b0010;
    else if (a inside {[10'd20:10'd24]}) exp_tr = 4'b0011;
    else if (a inside {[10'd25:10'd34]}) exp_tr = 4'b0100;
    else                                 exp_tr = 4'b0000;
  endfunction

  // Core functional equivalence
  ap_map:   assert property (temp_range == exp_tr(analog_in));

  // Output is always a legal code
  ap_legal: assert property (temp_range inside {4'b0000,4'b0001,4'b0010,4'b0011,4'b0100});

  // No X/Z on output
  ap_no_x:  assert property (!$isunknown(temp_range));

  // Functional coverage of all buckets and default
  cp_0:       cover property (analog_in == 10'd0               && temp_range == 4'b0000);
  cp_1_9:     cover property (analog_in inside {[1:9]}         && temp_range == 4'b0001);
  cp_10_19:   cover property (analog_in inside {[10:19]}       && temp_range == 4'b0010);
  cp_20_24:   cover property (analog_in inside {[20:24]}       && temp_range == 4'b0011);
  cp_25_34:   cover property (analog_in inside {[25:34]}       && temp_range == 4'b0100);
  cp_default: cover property (analog_in > 10'd34               && temp_range == 4'b0000);

  // Boundary transition coverage (adjacent range edges)
  cb_9_10:   cover property (analog_in == 10'd9  ##1 analog_in == 10'd10);
  cb_19_20:  cover property (analog_in == 10'd19 ##1 analog_in == 10'd20);
  cb_24_25:  cover property (analog_in == 10'd24 ##1 analog_in == 10'd25);
  cb_34_35:  cover property (analog_in == 10'd34 ##1 analog_in == 10'd35);
endchecker

// Example bind (ensure tb_clk is visible where you bind)
// bind temperature_sensor temperature_sensor_sva u_sva ( .clk(tb_clk), .analog_in(analog_in), .temp_range(temp_range) );