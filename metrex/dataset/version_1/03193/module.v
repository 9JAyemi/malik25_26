module RisingEdgeDetector(
    input in,
    output reg out,
    input clk
);

    reg prev_in;
    
    always @(posedge clk) begin
        if (in && !prev_in) begin
            out <= 1'b1;
        end else begin
            out <= 1'b0;
        end
        prev_in <= in;
    end
    
endmodule