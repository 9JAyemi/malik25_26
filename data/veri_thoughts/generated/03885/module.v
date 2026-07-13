module binary_counter (
    input CLK,
    input RST,
    input EN,
    output reg [3:0] q
);

    always @(posedge CLK or posedge RST) begin
        if (RST) begin
            q <= 4'b0000;
        end
        else if (EN) begin
            q <= q + 1;
        end
    end

endmodule