module cart
(
  input  wire           clk,
  input  wire           clk7_en,
  input  wire           clk7n_en,
  input  wire           cpu_rst,
  input  wire [ 24-1:1] cpu_address,
  input  wire [ 24-1:1] cpu_address_in,
  input  wire           _cpu_as,
  input  wire           cpu_rd,
  input  wire           cpu_hwr,
  input  wire           cpu_lwr,
  input  wire [ 32-1:0] cpu_vbr,
  input  wire [  9-1:1] reg_address_in,
  input  wire [ 16-1:0] reg_data_in,
  input  wire           dbr,
  input  wire           ovl,
  input  wire           freeze,
  output wire [ 16-1:0] cart_data_out,
  output reg            int7 = 1'b0,
  output wire           sel_cart,
  output wire           ovr,
output wire           aron
);


reg  [32-1:0] nmi_vec_adr=0;
reg           freeze_d=0;
wire          freeze_req;
wire          int7_req;
wire          int7_ack;
reg           l_int7_req=0;
reg           l_int7_ack=0;
reg           l_int7=0;
reg           active=0;
wire          sel_custom_mirror;
wire [16-1:0] nmi_adr_out;
reg  [16-1:0] custom_mirror_q;
wire [16-1:0] custom_mirror_out;
reg  [16-1:0] custom_mirror [0:256-1];


`define ARON_HACK
`ifndef ARON_HACK
always @ (posedge clk) begin
  if (clk7_en) begin
    if (cpu_rst && (cpu_address_in[23:19]==5'b1010_0) && cpu_lwr && !aron)
      aron <= 1'b1;
  end
end
`else
assign aron = 1'b1;
`endif

assign sel_cart = ~dbr && (cpu_address_in[23:19]==5'b1010_0); always @ (posedge clk) begin
  if (clk7_en) begin
    nmi_vec_adr <= #1 cpu_vbr + 32'h0000007c; end
end

assign ovr = active && ~dbr && ~ovl && cpu_rd && (cpu_address_in[23:2] == nmi_vec_adr[23:2]);

assign nmi_adr_out = ovr ? (!cpu_address_in[1] ? 16'h00a1 : 16'h000c) : 16'h0000;

always @ (posedge clk) begin
  if (clk7_en) begin
    freeze_d <= freeze;
  end
end

assign freeze_req = freeze && ~freeze_d;

assign int7_req =  freeze_req;

assign int7_ack = &cpu_address_in && ~_cpu_as;

always @ (posedge clk) begin
  if (clk7_en) begin
    if (cpu_rst)
      int7 <= 1'b0;
    else if (int7_req)
      int7 <= 1'b1;
    else if (int7_ack)
      int7 <= 1'b0;
  end
end

always @ (posedge clk) begin
  if (clk7_en) begin
    l_int7_req <= int7_req;
    l_int7_ack <= int7_ack;
  end
end

always @ (posedge clk) begin
  if (clk7_en) begin
    if (cpu_rst)
      l_int7 <= 1'b0;
    else if (l_int7_req)
      l_int7 <= 1'b1;
    else if (l_int7_ack && cpu_rd)
      l_int7 <= 1'b0;
  end
end

always @ (posedge clk) begin
  if (clk7_en) begin
    if (cpu_rst)
      active <= #1 1'b0;
    else if ( l_int7 && l_int7_ack && cpu_rd)
      active <= #1 1'b1;
    else if (sel_cart && cpu_rd)
      active <= #1 1'b0;
  end
end

assign sel_custom_mirror = ~dbr && cpu_rd && (cpu_address_in[23:12]==12'b1010_1001_1111); always @ (posedge clk) begin
  if (clk7_en) begin
    custom_mirror[reg_address_in] <= #1 reg_data_in;
  end
  custom_mirror_q <= #1 custom_mirror[cpu_address_in[8:1]];
end

assign custom_mirror_out = sel_custom_mirror ? custom_mirror_q : 16'h0000;

assign cart_data_out = custom_mirror_out | nmi_adr_out;


endmodule

