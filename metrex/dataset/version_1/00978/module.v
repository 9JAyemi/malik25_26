
module counter (
    input clk,
    input reset,
    output reg [3:0] counter_out
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            counter_out <= 4'b0000;
        end else begin
            counter_out <= counter_out + 4'b0001;
        end
    end

endmodule
module register (
    input clk,
    input reset,
    input [7:0] data_in,
    output reg [7:0] register_out
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            register_out <= 8'b00000000;
        end else begin
            register_out <= data_in;
        end
    end

endmodule
module functional_module (
    input [3:0] counter_out,
    input [7:0] register_out,
    output [7:0] final_output
);

    assign final_output = counter_out < register_out ? counter_out : register_out;

endmodule
module top_module (
    input clk,
    input reset,
    output [7:0] final_output
);

    wire [3:0] counter_out;
    wire [7:0] register_out;

    counter counter_inst (
        .clk(clk),
        .reset(reset),
        .counter_out(counter_out)
    );

    register register_inst (
        .clk(clk),
        .reset(reset),
        .data_in(final_output),
        .register_out(register_out)
    );

    functional_module functional_inst (
        .counter_out(counter_out),
        .register_out(register_out),
        .final_output(final_output)
    );

endmodule