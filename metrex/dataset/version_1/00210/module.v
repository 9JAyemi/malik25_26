module top_module (
    input clk,        // System clock
    input reset,      // Asynchronous active-high reset
    output reg out    // Output of the functional module
);

reg clk_divided;
reg [3:0] count;

// Edge detection module
always @(posedge clk) begin
    clk_divided <= ~clk_divided;
end

// 4-bit binary counter module
always @(posedge clk_divided or posedge reset) begin
    if (reset) begin
        count <= 4'b0000;
    end else begin
        count <= count + 1;
        if (count == 4'b1111) begin
            count <= 4'b0000;
        end
    end
end

// Functional module to generate square wave with 50% duty cycle
always @(posedge clk_divided or posedge reset) begin
    if (reset) begin
        out <= 1'b0;
    end else begin
        if (count < 4'b1000) begin
            out <= 1'b0;
        end else begin
            out <= 1'b1;
        end
    end
end

endmodule