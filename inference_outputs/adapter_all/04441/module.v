module infrared_control(
   input infrared,     input clk,          input reset,        output reg led,     output reg botao_1, output reg botao_2, output reg botao_3, output reg botao_4  );

   integer count; reg estado_atual;
   reg estado_prox;

   parameter IDLE  = 0; parameter PRESS = 1; parameter BOT14 = 2; parameter BOT23 = 3; parameter KEEP1 = 4; parameter KEEP2 = 5; parameter KEEP3 = 6; parameter KEEP4 = 7; parameter T_IGNOR = 57000; parameter T_PRESS = 950;   always@(posedge clk) begin
      if(infrared == 1) begin
         led = 1;
      end
      else begin
         led = 0;
      end
   end

   always@(posedge clk)begin
      case(estado_atual)
         PRESS: count = count + 1;
         BOT14: count = count + 1;
         BOT23: count = count + 1;
         KEEP1: count = count + 1;
         KEEP2: count = count + 1;
         KEEP3: count = count + 1;
         KEEP4: count = count + 1;
         default: count = 0;
      endcase
   end

   always@(*) begin
      case(estado_atual)
         IDLE: begin
            if(infrared == 1) begin
               estado_prox = PRESS;
            end
            else begin
               estado_prox = IDLE;
            end
         end
         PRESS: begin
            if(count >= 130) begin
               if(infrared == 1) begin
                  estado_prox = BOT14;
               end
               else begin
                  estado_prox = BOT23;
               end
            end
            else begin
               estado_prox = PRESS;
            end
         end
         BOT14: begin
            if(count >= 190) begin
               if(infrared == 1) begin
                  estado_prox = KEEP4;
               end
               else begin
                  estado_prox = KEEP1;
               end
            end
            else begin
               estado_prox = BOT14;
            end
         end
         BOT23: begin
            if(count >= 170) begin
               if(infrared == 1) begin
                  estado_prox = KEEP3;
               end
               else begin
                  estado_prox = KEEP2;
               end
            end
            else begin
               estado_prox = BOT23;
            end
         end
         KEEP1: begin
            if(count >= T_IGNOR) begin
               estado_prox = IDLE;
            end
            else begin
               estado_prox = KEEP1;
            end
         end
         KEEP2: begin
            if(count >= T_IGNOR) begin
               estado_prox = IDLE;
            end
            else begin
               estado_prox = KEEP2;
            end
         end
         KEEP3: begin
            if(count >= T_IGNOR) begin
               estado_prox = IDLE;
            end
            else begin
               estado_prox = KEEP3;
            end
         end
         KEEP4: begin
            if(count >= T_IGNOR) begin
               estado_prox = IDLE;
            end
            else begin
               estado_prox = KEEP4;
            end
         end
         default: begin
            estado_prox = IDLE;
         end
      endcase
   end

   always@(posedge clk) begin
      if(reset) begin
         estado_atual <= IDLE;
      end
      else begin
         estado_atual <= estado_prox;
      end
   end

   always@(*) begin
      case(estado_atual)
         BOT14: begin
            if(count >= 190) begin
               if(infrared == 1) begin
                  botao_1 = 0;
                  botao_2 = 0;
                  botao_3 = 0;
                  botao_4 = 1;
               end
               else begin
                  botao_1 = 1;
                  botao_2 = 0;
                  botao_3 = 0;
                  botao_4 = 0;
               end
            end
            else begin
               botao_1 = 0;
               botao_2 = 0;
               botao_3 = 0;
               botao_4 = 0;
            end
         end
         BOT23: begin
            if(count >= 170) begin
               if(infrared == 1) begin
                  botao_1 = 0;
                  botao_2 = 0;
                  botao_3 = 1;
                  botao_4 = 0;
               end
               else begin
                  botao_1 = 0;
                  botao_2 = 1;
                  botao_3 = 0;
                  botao_4 = 0;
               end
            end
            else begin
               botao_1 = 0;
               botao_2 = 0;
               botao_3 = 0;
               botao_4 = 0;
            end
         end
         KEEP1: begin
            if(count >= T_PRESS) begin
               botao_1 = 0;
               botao_2 = 0;
               botao_3 = 0;
               botao_4 = 0;
            end
            else begin
               botao_1 = 1;
               botao_2 = 0;
               botao_3 = 0;
               botao_4 = 0;
            end
         end
         KEEP2: begin
            if(count >= T_PRESS) begin
               botao_1 = 0;
               botao_2 = 0;
               botao_3 = 0;
               botao_4 = 0;
            end
            else begin
               botao_1 = 0;
               botao_2 = 1;
               botao_3 = 0;
               botao_4 = 0;
            end
         end
         KEEP3: begin
            if(count >= T_PRESS) begin
               botao_1 = 0;
               botao_2 = 0;
               botao_3 = 0;
               botao_4 = 0;
            end
            else begin
               botao_1 = 0;
               botao_2 = 0;
               botao_3 = 1;
               botao_4 = 0;
            end
         end
         KEEP4: begin
            if(count >= T_PRESS) begin
               botao_1 = 0;
               botao_2 = 0;
               botao_3 = 0;
               botao_4 = 0;
            end
            else begin
               botao_1 = 0;
               botao_2 = 0;
               botao_3 = 0;
               botao_4 = 1;
            end
         end
         default: begin
            botao_1 = 0;
            botao_2 = 0;
            botao_3 = 0;
            botao_4 = 0;
         end
      endcase
   end

endmodule
