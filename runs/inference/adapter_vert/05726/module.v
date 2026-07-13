
module binary_counter (
    input CLK,
    input CLR_B,
    input LOAD,
    input [4:0] DATA_IN,
    output reg [4:0] Q
);

parameter MAX_VALUE = 16;

always @(posedge CLK) begin
    if (CLR_B) begin
        Q <= 0;
    end else if (LOAD) begin
        Q <= DATA_IN;
    end else if (Q == MAX_VALUE - 1) begin
        Q <= 0;
    end else begin
        Q <= Q + 1;
    end
end

endmodule