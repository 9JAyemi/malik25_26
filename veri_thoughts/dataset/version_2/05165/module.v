
module binary_counter (
    input clk,
    input reset,
    output reg [3:0] counter_out
);

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            counter_out <= 4'b0000;
        end else begin
            counter_out <= counter_out + 1;
        end
    end

endmodule
module mux_2to1 (
    input [3:0] input_0,
    input [3:0] input_1,
    input select,
    output reg [3:0] mux_out
);

    always @(select) begin
        if (select) begin
            mux_out <= input_1;
        end else begin
            mux_out <= input_0;
        end
    end

endmodule
module comparator (
    input [3:0] in_0,
    input [3:0] in_1,
    output reg out
);

    always @(in_0, in_1) begin
        if (in_0 >= in_1) begin
            out <= 1;
        end else begin
            out <= 0;
        end
    end

endmodule
module pwm_generator (
    input clk,
    input reset,
    input [3:0] counter_out,
    input [3:0] adc_in,
    input select,
    output reg pwm_out
);

    wire [3:0] mux_out;
    wire comparator_out;

    mux_2to1 mux (
        .input_0(counter_out),
        .input_1(adc_in),
        .select(select),
        .mux_out(mux_out)
    );

    comparator comp (
        .in_0(mux_out),
        .in_1(adc_in),
        .out(comparator_out)
    );

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            pwm_out <= 0;
        end else begin
            if (pwm_out == 1'b1 && comparator_out == 1'b0) begin
                pwm_out <= 1'b0;
            end else if (pwm_out == 1'b0 && comparator_out == 1'b1) begin
                pwm_out <= 1'b1;
            end
        end
    end

endmodule