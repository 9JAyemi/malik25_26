

module sampler #(
  parameter integer DW = 32,  parameter integer CW = 24   )(
  input  wire          clk, 		input  wire          rst, 		input  wire          extClock_mode,	input  wire          wrDivider, 	input  wire [CW-1:0] config_data, 	input  wire          sti_valid,	input  wire [DW-1:0] sti_data, 	output reg           sto_valid, 	output reg  [DW-1:0] sto_data, 	output reg           ready50
);

reg next_sto_valid;
reg [DW-1:0] next_sto_data;

reg [CW-1:0] divider, next_divider; 
reg [CW-1:0] counter, next_counter;	wire counter_zero = ~|counter;


initial
begin
  divider = 0;
  counter = 0;
  sto_valid = 0;
  sto_data = 0;
end
always @ (posedge clk) 
begin
  divider   <= next_divider;
  counter   <= next_counter;
  sto_valid <= next_sto_valid;
  sto_data  <= next_sto_data;
end

always @*
begin
  next_divider = divider;
  next_counter = counter;
  next_sto_valid = 1'b0;
  next_sto_data = sto_data;

  if (extClock_mode)
    begin
      next_sto_valid = sti_valid;
      next_sto_data = sti_data;
    end
  else if (sti_valid && counter_zero)
    begin
      next_sto_valid = 1'b1;
      next_sto_data = sti_data;
    end

  if (wrDivider)
    begin
      next_divider = config_data[CW-1:0];
      next_counter = next_divider;
      next_sto_valid = 1'b0; end
  else if (sti_valid) 
    if (counter_zero)
      next_counter = divider;
    else next_counter = counter-1'b1;
end


always @(posedge clk) 
begin
  if (wrDivider)
    ready50 <= 1'b0; else if (counter_zero)
    ready50 <= 1'b1;
  else if (counter == divider[CW-1:1])
    ready50 <= 1'b0;
end

endmodule
