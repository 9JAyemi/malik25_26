module register_file(
    input [1:0] read_register_port_0,
    input [1:0] read_register_port_1,
    input [1:0] write_register,
    input [31:0] write_data,
    input write_enable,
    output reg [31:0] read_data_port_0,
    output reg [31:0] read_data_port_1
);

reg [31:0] registers [0:3];

always @(*)
begin
    read_data_port_0 = registers[read_register_port_0];
    read_data_port_1 = registers[read_register_port_1];
end

always @(posedge write_enable)
begin
    if (write_enable)
        registers[write_register] <= write_data;
end

endmodule