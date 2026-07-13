
module shift_register_4bit (
    input [3:0] A,
    input LOAD,
    input CLK,
    output reg [3:0] Q
);

always @(posedge CLK) begin
    if (LOAD) begin
        Q <= A;
    end
end

endmodule