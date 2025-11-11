
module top_module (
  input clk,
  input reset,      // Synchronous active-high reset
  input [2:0] load_data, // 3-bit input for the shift register
  input load, // Parallel load input for the shift register
  output serial_out // Serial output from the shift register
);

  reg [2:0] shift_reg;
  reg [63:0] jc_output;
  wire [2:0] sr_output;
  wire result;

  // Instantiate the Johnson counter module
  chatgpt_generate_JC_counter jc_counter (
    .clk(clk),
    .rst_n(reset),
    .Q(jc_output)
  );

  // Instantiate the shift register module
  shift_register shift_reg_inst (
    .clk(clk),
    .load(load),
    .load_data(load_data),
    .shift_in(jc_output[0]),
    .shift_out(sr_output)
  );

  // Instantiate the functional module
  functional_module func_inst (
    .jc_output(jc_output),
    .sr_output(sr_output),
    .result(result)
  );

  // Assign the serial output to the result of the shift register
  assign serial_out = sr_output[2];

endmodule
module chatgpt_generate_JC_counter(
  input                clk,
  input                rst_n,
  output reg  [63:0]   Q
);

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      Q <= 64'b1;
    end else begin
      Q <= {Q[62:0], ~Q[63]};
    end
  end

endmodule
module shift_register(
  input clk,
  input load,
  input [2:0] load_data,
  input shift_in,
  output reg [2:0] shift_out
);

  always @(posedge clk) begin
    if (load) begin
      shift_out <= load_data;
    end else begin
      shift_out <= {shift_out[1:0], shift_in};
    end
  end

endmodule
module functional_module(
  input [63:0] jc_output, // Output from Johnson counter
  input [2:0] sr_output, // Output from shift register
  output reg result // XOR of the two inputs
);

  always @* begin
    result = jc_output[0] ^ sr_output[0];
  end

endmodule