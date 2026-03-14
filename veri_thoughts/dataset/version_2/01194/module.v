
module uparc_fwdu(
    rs,
    rs_data,
    rt,
    rt_data,
    rd_p2,
    rd_data_p2,
    pend_mem_load_p2,
    rd_p3,
    rd_data_p3,
    rs_data_p1,
    rt_data_p1
);

input wire [4:0] rs;
input wire [31:0] rs_data;
input wire [4:0] rt;
input wire [31:0] rt_data;

input wire [4:0] rd_p2;
input wire [31:0] rd_data_p2;

input wire pend_mem_load_p2;

input wire [4:0] rd_p3;
input wire [31:0] rd_data_p3;

output reg [31:0] rs_data_p1;
output reg [31:0] rt_data_p1;

always @(*) begin
    if (rs == rd_p2) begin
        rs_data_p1 = rd_data_p2;
    end else if (rs == rd_p3) begin
        rs_data_p1 = rd_data_p3;
    end else begin
        rs_data_p1 = rs_data;
    end
end

always @(*) begin
    if (rt == rd_p2 && !pend_mem_load_p2) begin
        rt_data_p1 = rd_data_p2;
    end else if (rt == rd_p3) begin
        rt_data_p1 = rd_data_p3;
    end else begin
        rt_data_p1 = rt_data;
    end
end

endmodule