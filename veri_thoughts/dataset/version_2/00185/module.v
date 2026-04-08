module shift_register (
    input CLK,
    input LOAD,
    input [3:0] DATA,
    output reg [3:0] Q
);

reg [3:0] reg_out;

always @(posedge CLK) begin
    if (LOAD) begin
        reg_out <= DATA;
    end else begin
        reg_out <= {reg_out[2:0], 1'b0};
    end
end

always @(*) begin
    Q = reg_out;
end

endmodule