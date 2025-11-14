module LTZ_CDCF #(
    parameter                WIDTH   = 1,
    parameter  [WIDTH -1:0]  INITVAL = {WIDTH{1'b0}}
) (
    input                    rst_n ,
    input                    clk   ,
    input      [WIDTH -1:0]  din   ,
    output reg [WIDTH -1:0]  dout
);

//
reg  [WIDTH -1:0]  buff ;
reg         [1:0]  state;

//
always @(posedge clk or negedge rst_n)
if (!rst_n)
    buff <= INITVAL;
else
    buff <= din;

//
always @(posedge clk or negedge rst_n)
if (!rst_n)
    dout <= INITVAL;
else if (state == 2'd3)
    dout <= buff;

// filter and judger
wire  neq = (buff != dout);
wire   eq = (buff == din );

always @(posedge clk or negedge rst_n)
if (!rst_n)
    state <= 2'b0;
else begin
    case (state)
        2'd0 : if (neq) state <= 2'd1;
        2'd1 : if ( eq) state <= 2'd2;
        2'd2 : if ( eq) state <= 2'd3; else state <= 2'd1;
        2'd3 : state <= 2'd0;
    endcase
end

//
endmodule