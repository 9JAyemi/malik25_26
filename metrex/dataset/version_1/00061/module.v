
module bram_controller(clk, reset, btn, wea, addra);

  input wire clk, reset, btn;
  output reg wea;
  output reg [3:0] addra;

  localparam [1:0]
  idle = 2'b00,
  leer = 2'b01,
  fin  = 2'b10;

  reg [1:0] state_reg;
  reg [3:0] counter;
  
  always@(posedge clk, posedge reset)
    if(reset)
      begin
        addra<=0;
        counter<=0;	
        state_reg<=idle;
        wea<=0;
      end
  else begin

    case(state_reg)

      idle:
        if(btn==1'b1)begin
          state_reg<=leer;
        end

      leer:
        begin
          wea<=0;
          counter<=counter+1'b1;
          state_reg<=fin;
        end

      fin:begin

        addra<=addra+1'b1;
        if(counter==4'b1111)begin
          counter<=0;
        end
        state_reg<=idle;
      end	

    endcase
  end
  
endmodule
