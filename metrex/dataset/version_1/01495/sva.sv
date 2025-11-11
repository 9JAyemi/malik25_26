// SVA checker for threshold_module
module threshold_module_sva #(parameter int THRESHOLD = 10)
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  input_value,
  input  logic [1:0]  output_value
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Sanity on parameter vs. input width
  initial begin
    assert (THRESHOLD >= 0) else $error("THRESHOLD must be >= 0");
    assert (THRESHOLD <= 16) else $error("THRESHOLD must be <= 16 for 4-bit input");
  end

  // No X/Z and legal encoding only
  assert property (!$isunknown(output_value));
  assert property (output_value inside {2'b00,2'b01,2'b10});

  // Exact decode (accounts for else-if priority)
  assert property ( (input_value <= 4'd5) <-> (output_value == 2'b00) );
  assert property ( ((input_value > 4'd5) && (input_value >= THRESHOLD)) <-> (output_value == 2'b10) );
  assert property ( ((input_value > 4'd5) && (input_value < THRESHOLD)) <-> (output_value == 2'b01) );

  // Determinism: same input => same output
  assert property ( $past(rst_n) && (input_value == $past(input_value)) |-> (output_value == $past(output_value)) );

  // Coverage: regions and key boundaries
  cover property (input_value <= 4'd5 && output_value == 2'b00);
  cover property ((input_value > 4'd5) && (input_value < THRESHOLD) && output_value == 2'b01);
  cover property ((input_value > 4'd5) && (input_value >= THRESHOLD) && output_value == 2'b10);

  cover property (input_value == 4'd0 && output_value == 2'b00);
  cover property (input_value == 4'd5 && output_value == 2'b00);
  cover property (input_value == 4'd6 && output_value == 2'b01);

  cover property ( (THRESHOLD > 0 && THRESHOLD <= 15) &&
                   (input_value == (THRESHOLD-1)) && output_value == 2'b01 );
  cover property ( (THRESHOLD <= 15) &&
                   (input_value == THRESHOLD[3:0]) && output_value == 2'b10 );

  cover property (input_value == 4'd15 &&
                  (((4'd15 > 4'd5) && (15 >= THRESHOLD)) ? output_value == 2'b10 :
                                                         ((4'd15 > 4'd5) && (15 < THRESHOLD))  ? output_value == 2'b01 :
                                                                                                 output_value == 2'b00));
endmodule

// Bind into DUT (provide clk and rst_n from your environment)
bind threshold_module threshold_module_sva #(.THRESHOLD(THRESHOLD))
  u_threshold_module_sva (.clk(clk), .rst_n(rst_n), .input_value(input_value), .output_value(output_value));