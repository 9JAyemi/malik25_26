module trigterm_range_bit (
  input  wire sti_data,
  input  wire clk,
  input  wire wrenb,
  input  wire din,
  output wire dout,
  input  wire cin,
  output wire cout,
  output wire hit
);

wire       hit_internal;
reg [15:0] mem;

always @(posedge clk)
if (wrenb) mem <= {mem, din};

assign hit_internal  = mem[{3'b000, sti_data}];
assign dout = mem[15];

assign hit = hit_internal;
assign cout = hit_internal ? cin : din;

endmodule