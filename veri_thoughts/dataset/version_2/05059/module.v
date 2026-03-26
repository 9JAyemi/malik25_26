module ldly1_5us(
    input clk, reset, in,
    output reg p,
    output reg l
);

    reg [7:0] r;
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            r <= 0;
            l <= 0;
        end else begin
            if (in) begin
                r <= 1;
                l <= 1;
                p <= 0;
            end else if (p) begin
                r <= 0;
                l <= 0;
            end else if (r == 75) begin
                p <= 1;
            end else begin
                r <= r + 1;
                l <= 0;
            end
        end
    end
    
endmodule