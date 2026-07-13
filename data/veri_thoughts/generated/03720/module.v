module traffic_light_fsm(
  input clk,
  input reset,
  output reg NSG_LED,
  output reg EWG_LED,
  output reg yellow_LED
);

  // Define the states
  parameter NSG = 2'b00;
  parameter NSG_YELLOW = 2'b01;
  parameter EWG = 2'b10;
  parameter EWG_YELLOW = 2'b11;

  // Define the state register and initialize to NSG
  reg [1:0] state_reg = NSG;

  // Define the state output logic
  always @ (state_reg) begin
    case (state_reg)
      NSG: begin
        NSG_LED = 1;
        EWG_LED = 0;
        yellow_LED = 0;
      end
      NSG_YELLOW: begin
        NSG_LED = 0;
        EWG_LED = 0;
        yellow_LED = 1;
      end
      EWG: begin
        NSG_LED = 0;
        EWG_LED = 1;
        yellow_LED = 0;
      end
      EWG_YELLOW: begin
        NSG_LED = 0;
        EWG_LED = 0;
        yellow_LED = 1;
      end
    endcase
  end

  // Define the state transition logic
  always @ (posedge clk, posedge reset) begin
    if (reset) begin
      state_reg <= NSG;
    end else begin
      case (state_reg)
        NSG: begin
          if (count == 30) begin
            state_reg <= NSG_YELLOW;
            count <= 0;
          end else begin
            count <= count + 1;
          end
        end
        NSG_YELLOW: begin
          if (count == 5) begin
            state_reg <= EWG;
            count <= 0;
          end else begin
            count <= count + 1;
          end
        end
        EWG: begin
          if (count == 20) begin
            state_reg <= EWG_YELLOW;
            count <= 0;
          end else begin
            count <= count + 1;
          end
        end
        EWG_YELLOW: begin
          if (count == 5) begin
            state_reg <= NSG;
            count <= 0;
          end else begin
            count <= count + 1;
          end
        end
      endcase
    end
  end

  // Define the count register and initialize to 0
  reg [5:0] count = 0;

endmodule
