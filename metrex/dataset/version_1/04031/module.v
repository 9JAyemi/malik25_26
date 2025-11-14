module shift_register (
    input clk,
    input [3:0] data_in,
    input shift_right,
    input load,
    output reg [3:0] data_out
);

reg [3:0] register;

always @(posedge clk) begin
    if (load) begin
        register <= data_in;
    end else begin
        if (shift_right) begin
            register <= {register[2:0], register[3]};
        end else begin
            register <= {register[3], register[2:0]};
        end
    end
end

always @* begin
    data_out = register;
end

endmodule