module shift_register (
    input [3:0] DATA_IN,
    input SHIFT_EN,
    input LOAD_EN,
    input CLK,
    output [3:0] DATA_OUT
);

reg [3:0] register;

always @(posedge CLK) begin
    if (LOAD_EN) begin
        register <= DATA_IN;
    end else if (SHIFT_EN) begin
        register <= {register[2:0], register[3]};
    end
end

assign DATA_OUT = register;

endmodule