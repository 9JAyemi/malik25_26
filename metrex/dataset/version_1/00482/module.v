module fifo_address_sync (
	input clk,
	input resetn,

	input m_axis_ready,
	output reg m_axis_valid,
	output reg  [C_ADDRESS_WIDTH-1:0] m_axis_raddr,
	output reg [C_ADDRESS_WIDTH-1:0] m_axis_raddr_next,
	output [C_ADDRESS_WIDTH:0] m_axis_level,

	output reg s_axis_ready,
	input s_axis_valid,
	output reg s_axis_empty,
	output reg [C_ADDRESS_WIDTH-1:0] s_axis_waddr,
	output [C_ADDRESS_WIDTH:0] s_axis_room
);

parameter C_ADDRESS_WIDTH = 4;

reg [C_ADDRESS_WIDTH:0] room = 2**C_ADDRESS_WIDTH;
reg [C_ADDRESS_WIDTH:0] level = 'h00;
reg [C_ADDRESS_WIDTH:0] level_next;

assign s_axis_room = room;
assign m_axis_level = level;

wire read = m_axis_ready & m_axis_valid;
wire write = s_axis_ready & s_axis_valid;

always @(*)
begin
	if (read)
		m_axis_raddr_next <= m_axis_raddr + 1'b1;
	else
		m_axis_raddr_next <= m_axis_raddr;
end

always @(posedge clk)
begin
	if (resetn == 1'b0) begin
		s_axis_waddr <= 'h00;
		m_axis_raddr <= 'h00;
	end else begin
		if (write)
			s_axis_waddr <= s_axis_waddr + 1'b1;
		m_axis_raddr <= m_axis_raddr_next;
	end
end

always @(*)
begin
	if (read & ~write)
		level_next <= level - 1'b1;
	else if (~read & write)
		level_next <= level + 1'b1;
	else
		level_next <= level;
end

always @(posedge clk)
begin
	if (resetn == 1'b0) begin
		m_axis_valid <= 1'b0;
		s_axis_ready <= 1'b0;
		level <= 'h00;
		room <= 2**C_ADDRESS_WIDTH;
		s_axis_empty <= 'h00;
	end else begin
		level <= level_next;
		room <= 2**C_ADDRESS_WIDTH - level_next;
		m_axis_valid <= level_next != 0;
		s_axis_ready <= level_next != 2**C_ADDRESS_WIDTH;
		s_axis_empty <= level_next == 0;
	end
end

endmodule

