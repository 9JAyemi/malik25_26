// SVA bind file for top_module and submodules

// 1) Johnson counter checks (function and reset)
module jc_counter_sva(input clk, input rst_n, input [63:0] Q);
  default clocking cb @(posedge clk); endclocking

  // Async active-low reset drives Q to 64'b1 whenever low at a sample
  assert property (@(posedge clk) !rst_n |-> (Q == 64'b1));

  // Step behavior when not in reset (guard that previous cycle was not in reset)
  assert property (@(posedge clk) rst_n && $past(rst_n) |-> Q == { $past(Q)[62:0], ~$past(Q)[63] });

  // Coverage: see reset, MSB rising/falling, and recurrence to initial state
  cover property (@(posedge clk) !rst_n ##1 rst_n);                 // reset release
  cover property (@(posedge clk) rst_n && $rose(Q[63]));
  cover property (@(posedge clk) rst_n && $fell(Q[63]));
  cover property (@(posedge clk) rst_n && Q == 64'b1 ##[1:$] Q == 64'b1);
endmodule

bind chatgpt_generate_JC_counter jc_counter_sva(.clk(clk), .rst_n(rst_n), .Q(Q));


// 2) Shift-register checks (load and shift behavior)
module shift_register_sva(input clk, input load, input [2:0] load_data,
                          input shift_in, input [2:0] shift_out);
  default clocking cb @(posedge clk); endclocking

  // Make $past safe at time 0
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // On load, next value equals load_data sampled in the same cycle
  assert property (past_valid && load |=> shift_out == $past(load_data));

  // On shift, next value equals {prev[1:0], prev shift_in}
  assert property (past_valid && !load |=> shift_out == { $past(shift_out[1:0]), $past(shift_in) });

  // Coverage: exercise both paths and both shift_in values
  cover property (past_valid && load);
  cover property (past_valid && !load && shift_in == 1'b0);
  cover property (past_valid && !load && shift_in == 1'b1);
endmodule

bind shift_register shift_register_sva(.clk(clk), .load(load), .load_data(load_data),
                                       .shift_in(shift_in), .shift_out(shift_out));


// 3) Functional module check (pure combinational XOR)
module functional_module_sva(input [63:0] jc_output, input [2:0] sr_output, input result);
  // Immediate assertion is appropriate for pure combinational behavior
  always @* assert (result == (jc_output[0] ^ sr_output[0]));
  // Coverage: both XOR outcomes occur
  cover property (@(posedge $global_clock) result == 1'b0);
  cover property (@(posedge $global_clock) result == 1'b1);
endmodule

bind functional_module functional_module_sva(.jc_output(jc_output), .sr_output(sr_output), .result(result));


// 4) Top-level integration checks (connectivity and polarity)
module top_integration_sva(input clk, input reset, input load, input [2:0] load_data,
                           input serial_out, input [63:0] jc_output, input [2:0] sr_output);
  default clocking cb @(posedge clk); endclocking

  // Connectivity: serial_out is MSB of shift register
  assert property (serial_out == sr_output[2]);

  // Integration of JC bit into shifter on shift cycles (ties two modules together)
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  assert property (past_valid && !load |=> sr_output == { $past(sr_output[1:0]), $past(jc_output[0]) });

  // Note: The JC sees an active-low reset (rst_n). Top's 'reset' is wired directly.
  // These assertions document and verify that effective reset is active-low at the top.
  assert property (!reset |-> (jc_output == 64'b1)); // when reset=0, JC is held in reset value
  assert property (reset && $past(reset) |-> jc_output == { $past(jc_output)[62:0], ~$past(jc_output)[63] });

  // Coverage: observe serial_out activity
  cover property ($changed(serial_out));
endmodule

bind top_module top_integration_sva(.clk(clk), .reset(reset), .load(load), .load_data(load_data),
                                    .serial_out(serial_out), .jc_output(jc_output), .sr_output(sr_output));