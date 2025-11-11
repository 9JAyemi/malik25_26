module game_graph
   (
    input wire clk, reset,
    input wire video_on,
    input wire [2:0] sw,
    input wire gra_still,
    input wire [9:0] pix_x, pix_y,
    output reg hit, miss, kill,
    output wire graph_on,
    output reg [2:0] graph_rgb
   );

   localparam MAX_X = 640;
   localparam MAX_Y = 480;
   wire refr_tick;
   localparam WALL_X_L = 20;
   localparam WALL_X_R = 25;
   localparam GUN_X_L = 50;
   localparam GUN_X_R = 53;
   wire [9:0] gun_y_t;
   wire [9:0] gun_y_b;
   reg [9:0] gun_y_reg;
   reg [9:0] gun_y_next;
   localparam GUN_V = 2;
   localparam GUN_Y_SIZE = 62;
   localparam BULLET_SIZE = 9;
   localparam BULLET_V = 5;
   wire [9:0] bullet_x_l, bullet_x_r;
   wire [9:0] bullet_y_t, bullet_y_b;
   reg [9:0] bullet_x_reg;
   reg [9:0] bullet_y_reg; 
   reg [9:0] bullet_x_next;
   reg [9:0] bullet_y_next;      
   localparam BAR_X_L = 600;
   localparam BAR_X_R = 603;
   wire [9:0] bar_y_t, bar_y_b;
   localparam BAR_Y_SIZE = 72;
   reg [9:0] bar_y_reg, bar_y_next;
   localparam BAR_V = 4;
   localparam BALL_SIZE = 8;
   wire [9:0] ball_x_l, ball_x_r;
   wire [9:0] ball_y_t, ball_y_b;
   reg [9:0] ball_x_reg, ball_y_reg;
   wire [9:0] ball_x_next, ball_y_next;
   reg [9:0] x_delta_reg, x_delta_next;
   reg [9:0] y_delta_reg, y_delta_next;
   localparam BALL_V_P = 2;
   localparam BALL_V_N = -2;
   wire [2:0] rom_addr, rom_col;
   reg [7:0] rom_data;
   wire rom_bit;
   wire wall_on, bar_on, gun_on, bullet_on, sq_ball_on, rd_ball_on;
   wire [2:0] wall_rgb, gun_rgb, bullet_rgb, bar_rgb, ball_rgb;

   always @*
   case (rom_addr)
      3'h0: rom_data = 8'b00111100; 3'h1: rom_data = 8'b01111110; 3'h2: rom_data = 8'b11111111; 3'h3: rom_data = 8'b11111111; 3'h4: rom_data = 8'b11111111; 3'h5: rom_data = 8'b11111111; 3'h6: rom_data = 8'b01111110; 3'h7: rom_data = 8'b00111100; endcase

   always @(posedge clk, posedge reset)
      if (reset)
         begin
            bar_y_reg <= 0;
            gun_y_reg <= 0;
            ball_x_reg <= 0;
            ball_y_reg <= 0;
            bullet_x_reg <= GUN_X_R;
            bullet_y_reg <= 0+GUN_Y_SIZE/2; 
            x_delta_reg <= 10'h004;
            y_delta_reg <= 10'h004;
         end
      else
         begin
            bar_y_reg <= bar_y_next;
            gun_y_reg <= gun_y_next;
            ball_x_reg <= ball_x_next;
            ball_y_reg <= ball_y_next;
            x_delta_reg <= x_delta_next;
            y_delta_reg <= y_delta_next;
            bullet_x_reg <= bullet_x_next; bullet_y_reg <= bullet_y_next;
            end

   assign refr_tick = (pix_y==481) && (pix_x==0);

   assign wall_on = (WALL_X_L<=pix_x) && (pix_x<=WALL_X_R);
   assign wall_rgb = 3'b001; assign bar_y_t = bar_y_reg;
   assign bar_y_b = bar_y_t + BAR_Y_SIZE - 1;
   assign bar_on = (BAR_X_L<=pix_x) && (pix_x<=BAR_X_R) &&
                   (bar_y_t<=pix_y) && (pix_y<=bar_y_b);
   assign bar_rgb = 3'b010; always @*
   begin
      bar_y_next = bar_y_reg; if(gra_still)
         bar_y_next = (MAX_Y-BAR_Y_SIZE)/2;
      else if (refr_tick)
         if (~sw[2] & (bar_y_b < (MAX_Y-1-BAR_V)))
            bar_y_next = bar_y_reg + BAR_V; else if (sw[2] & (bar_y_t > BAR_V))
            bar_y_next = bar_y_reg - BAR_V; end
   assign gun_y_t = gun_y_reg;
   assign gun_y_b = gun_y_t + GUN_Y_SIZE -1;
   assign gun_on = (GUN_X_L<=pix_x) && (pix_x<=GUN_X_R) && (gun_y_t<=pix_y) && (pix_y<=gun_y_b);
   assign gun_rgb = 3'b000;
   always @*
   begin
      gun_y_next = gun_y_reg;
      if(gra_still)
         gun_y_next = (MAX_Y-GUN_Y_SIZE)/2;        
      else if (refr_tick)
         if (sw[0] & (gun_y_b < (MAX_Y-1-GUN_V)))
            gun_y_next = gun_y_reg + GUN_V; else if ( (~sw[0]) & (gun_y_t > GUN_V) )
            gun_y_next = gun_y_reg - GUN_V; end
   assign bullet_x_l = bullet_x_reg;
   assign bullet_x_r = bullet_x_l + BULLET_SIZE -1;
   assign bullet_y_t = bullet_y_reg;
   assign bullet_y_b = bullet_y_t + BULLET_SIZE -1;
   
   assign bullet_on =
            (bullet_x_l<=pix_x) && (pix_x<=bullet_x_r) &&
            (bullet_y_t<=pix_y) && (pix_y<=bullet_y_b);
   assign bullet_rgb = 3'b000; always @*
   begin
      kill = 1'b0;
      bullet_x_next = bullet_x_reg;
      bullet_y_next = bullet_y_reg;
      if(gra_still)
         begin
            bullet_x_next = GUN_X_R;
            bullet_y_next = (MAX_Y-GUN_Y_SIZE)/2 + GUN_Y_SIZE/2; 
         end
      else if (refr_tick)      
         if ((BAR_X_L<=bullet_x_r) && (bullet_x_r<=BAR_X_R) &&
               (bar_y_t<=bullet_y_b) && (bullet_y_t<=bar_y_b))
         begin
               bullet_x_next = GUN_X_R;
               bullet_y_next = gun_y_reg+GUN_Y_SIZE/2;
               kill = 1'b1;
               end
         else if ( sw[1] || (bullet_x_l >= GUN_X_R+5) )
            bullet_x_next = bullet_x_reg + BULLET_V; 
         else if ( (bullet_x_reg<=(GUN_X_L-1)) || (bullet_x_reg>=(MAX_X-BULLET_SIZE-1)) ) 
         begin
            bullet_x_next = GUN_X_R;
            bullet_y_next = gun_y_reg+GUN_Y_SIZE/2;
            end            
         else
            begin
            bullet_x_next = GUN_X_R;
            bullet_y_next = gun_y_reg+GUN_Y_SIZE/2;
            end         
   end
   assign ball_x_l = ball_x_reg;
   assign ball_y_t = ball_y_reg;
   assign ball_x_r = ball_x_l + BALL_SIZE - 1;
   assign ball_y_b = ball_y_t + BALL_SIZE - 1;
   assign sq_ball_on =
            (ball_x_l<=pix_x) && (pix_x<=ball_x_r) &&
            (ball_y_t<=pix_y) && (pix_y<=ball_y_b);
   assign rom_addr = pix_y[2:0] - ball_y_t[2:0];
   assign rom_col = pix_x[2:0] - ball_x_l[2:0];
   assign rom_bit = rom_data[rom_col];
   assign rd_ball_on = sq_ball_on & rom_bit;
   assign ball_rgb = 3'b100;   assign ball_x_next = (gra_still) ? MAX_X/2 :
                        (refr_tick) ? ball_x_reg+x_delta_reg :
                        ball_x_reg ;
   assign ball_y_next = (gra_still) ? MAX_Y/2 :
                        (refr_tick) ? ball_y_reg+y_delta_reg :
                        ball_y_reg ;
   always @*
   begin
      hit = 1'b0;
      miss = 1'b0;
      x_delta_next = x_delta_reg;
      y_delta_next = y_delta_reg;
      if (gra_still)     begin
            x_delta_next = BALL_V_N;
            y_delta_next = BALL_V_P;
         end   
      else if (ball_y_t < 1) y_delta_next = BALL_V_P;
      else if (ball_y_b > (MAX_Y-1)) y_delta_next = BALL_V_N;
      else if (ball_x_l <= WALL_X_R) x_delta_next = BALL_V_P;    else if ((BAR_X_L<=ball_x_r) && (ball_x_r<=BAR_X_R) &&
               (bar_y_t<=ball_y_b) && (ball_y_t<=bar_y_b))
         begin
            x_delta_next = BALL_V_N;  
            hit = 1'b1;
         end
      else if (ball_x_r>MAX_X)   miss = 1'b1;            end 
   always @*
      if (~video_on)
         graph_rgb = 3'b000; else
         if (wall_on)
            graph_rgb = wall_rgb;
         else if (bullet_on)
            graph_rgb = bullet_rgb;         
         else if (bar_on)
            graph_rgb = bar_rgb;
         else if (gun_on)
            graph_rgb = gun_rgb;
         else if (rd_ball_on)
         graph_rgb = ball_rgb;
         else
            graph_rgb = 3'b110; assign graph_on = wall_on | bar_on | rd_ball_on | bullet_on | gun_on;
   endmodule
