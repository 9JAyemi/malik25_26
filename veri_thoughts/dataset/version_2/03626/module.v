module binary_counter(
    input CLK, 
    input RESET, 
    output reg [3:0] Q
);

    always @(posedge CLK, negedge RESET) begin
        if (!RESET) begin
            Q <= 4'b0000;
        end
        else begin
            Q <= Q + 1;
        end
    end

endmodule