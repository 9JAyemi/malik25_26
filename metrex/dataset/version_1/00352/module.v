module counter_module (
    input clk, // Clock input
    input reset, // Reset signal input
    output reg [3:0] counter // 4-bit counter output
);

    always @(posedge clk) begin
        if (reset) begin
            counter <= 4'b0000;
        end else begin
            counter <= counter + 1;
        end
    end

endmodule

module final_output_module (
    input [3:0] counter, // 4-bit counter output
    input select, // Select input to choose between counter value and its complement
    output reg final_output // Final output based on select input
);

    always @(*) begin
        if (select) begin
            final_output <= ~counter;
        end else begin
            final_output <= counter;
        end
    end

endmodule

module top_module (
    input clk, // Clock input
    input reset, // Reset signal input
    input select, // Select input to choose between counter value and its complement
    output reg [3:0] counter, // 4-bit counter output
    output reg final_output // Final output based on select input
);

    counter_module counter_inst (
        .clk(clk),
        .reset(reset),
        .counter(counter)
    );

    final_output_module final_output_inst (
        .counter(counter),
        .select(select),
        .final_output(final_output)
    );

endmodule