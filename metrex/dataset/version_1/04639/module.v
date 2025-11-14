module DUC #(
    parameter INPUT_WIDTH = 8,
    parameter OUTPUT_WIDTH = 8,
    parameter INTERPOLATION_FACTOR = 4 
)(
    input wire clk,
    input wire reset,
    input wire [INPUT_WIDTH-1:0] in_signal,
    output reg [OUTPUT_WIDTH-1:0] out_signal
);

    reg [INPUT_WIDTH-1:0] interpolated_signal;
    integer i_count = 0;
    always @(posedge clk) begin
        if (reset) begin
            i_count <= 0;
            interpolated_signal <= 0;
        end else begin
            if (i_count < INTERPOLATION_FACTOR-1) begin
                interpolated_signal <= 0; // Zero-stuffing
                i_count <= i_count + 1;
            end else begin
                interpolated_signal <= in_signal; // Actual signal sample
                i_count <= 0;
            end
        end
    end
    
    reg [OUTPUT_WIDTH-1:0] filtered_signal;
    always @(posedge clk) begin
        filtered_signal <= (interpolated_signal + out_signal) >> 1;
    end

    always @(posedge clk) begin
        if (reset) begin
            out_signal <= 0;
        end else begin
            out_signal <= filtered_signal ^ {OUTPUT_WIDTH{1'b1}}; 
        end
    end

endmodule
