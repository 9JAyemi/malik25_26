module johnson_counter_and (
    input logic clk,
    input logic reset,
    input logic [7:0] input_val,
    output logic [63:0] output_val
);

reg [63:0] counter;

always @(posedge clk) begin
    if (reset) begin
        counter <= 64'b0000_0000_0000_0000_0000_0000_0000_0000;
    end else begin
        counter <= {counter[62:0], counter[63] ^ counter[0]};
    end
end

assign output_val = counter & {64{input_val}};

    ///// Johnson Counter Behavior /////
    // Counter increments on each clock edge when reset is LOW.
    counter_increment: assert property (
        @(posedge clk) disable iff (!reset) counter[63] == 1'b0
    );

    // Counter wraps around to 0 when the most significant bit is 1.
    counter_wrap: assert property (
        @(posedge clk) disable iff (!reset) counter[63] == 1'b1 |-> counter == 64'b0000_0000_0000_0000_0000_0000_0000_0000
    );

    // Counter is updated on each clock edge.
    counter_update: assert property (
        @(posedge clk) disable iff (!reset) counter[63] == 1'b0 |-> counter != counter[62:0]
    );

    // Output_val is the bitwise AND of the counter and the input_val repeated 64 times.
    output_val_behavior: assert property (
        @(posedge clk) disable iff (!reset) output_val == (counter & {64{input_val}})
    );

    // Counter is always 64 bits wide.
    counter_width: assert property (
        @(posedge clk) disable iff (!reset) counter == 64'b0000_0000_0000_0000_0000_0000_0000_0000 |-> counter[63:0] == 64'b0000_0000_0000_0000_0000_0000_0000_0000
    );

    // Counter is always 64 bits wide.
    counter_width_2: assert property (
        @(posedge clk) disable iff (!reset) counter == 64'bFFFFFFFFFFFFFFFF |-> counter[63:0] == 64'bFFFFFFFFFFFFFFFF
    );

    // Counter is always 64 bits wide.
    counter_width_3: assert property (
        @(posedge clk) disable iff (!reset) counter == 64'b8000000000000000 |-> counter[63:0] == 64'b8000000000000000
    );

    // Counter is always 64 bits wide.
    counter_width_4: assert property (
        @(posedge clk) disable iff (!reset) counter == 64'b4000000000000000 |-> counter[63:0] == 64'b4000000000000000
    );

    // Counter is always 64 bits wide.
    counter_width_5: assert property (
        @(posedge clk) disable iff (!reset) counter == 64'b2000000000000000 |-> counter[63:0] == 64'b2000000000000000
    );

    // Counter is always 64 bits wide.
    counter_width_6: assert property (
        @(posedge clk) disable iff (!reset) counter == 64'b1000000000000000 |-> counter[63:0] == 64'b1000000000000000
    );

endmodule