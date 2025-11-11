
module teclado(
    input      [7:0] ps2_data,
    output reg [4:0] val,
    output reg [2:0] control,
output [7:0] leds
  );
    
    
    localparam CTRL_NUMERO    = 3'd1;
    localparam CTRL_ENTER     = 3'd2;
    localparam CTRL_FLECHA    = 3'd3;
    localparam CTRL_OPERACION = 3'd4;
    
    localparam CERO   = 8'h45;
    localparam UNO    = 8'h16;
    localparam DOS    = 8'h1E;
    localparam TRES   = 8'h26;
    localparam CUATRO = 8'h25;
    localparam CINCO  = 8'h2E;
    localparam SEIS   = 8'h36;
    localparam SIETE  = 8'h3D;
    localparam OCHO   = 8'h3E;
    localparam NUEVE  = 8'h46;
    localparam A      = 8'h1C;
    localparam B      = 8'h32;
    localparam C      = 8'h21;
    localparam D      = 8'h23;
    localparam E      = 8'h24;
    localparam F      = 8'h2B;
    localparam O      = 8'h44;
    localparam Y      = 8'h35;
    localparam SUMA   = 8'h1B;
    localparam RESTA  = 8'h2D;
    localparam MUL    = 8'h3A;
    localparam ENTER  = 8'h5A;
    localparam ARRIBA    =8'h75;
    localparam ABAJO     =8'h72;
    localparam IZQUIERDA =8'h6B;
    localparam DERECHA   =8'h74;
     
    wire reloj_lento;
    
    
    assign leds[4:0]= val;
    assign leds[7:5]= control;   
    

   
    
    
    always @(*) begin
        case(ps2_data)
           CERO: begin
                    val=5'd0;        
                    control=CTRL_NUMERO;
            end
            UNO: begin
                    val=5'd1;
                    control=CTRL_NUMERO;
            end
            DOS:begin
                    val=5'd2;    
                    control=CTRL_NUMERO;
            end
            TRES:begin
                    val=5'd3;    
                    control=CTRL_NUMERO;
            end
            CUATRO:begin
                    val=5'd4;    
                    control=CTRL_NUMERO;
            end
            CINCO:begin
                    val=5'd5;    
                    control=CTRL_NUMERO;
            end
            SEIS:begin
                    val=5'd6;    
                    control=CTRL_NUMERO;
            end
            SIETE:begin
                    val=5'd7;    
                    control=CTRL_NUMERO;
            end
            OCHO:begin
                    val=5'd8;    
                    control=CTRL_NUMERO;
            end
            NUEVE:begin
                    val=5'd9;    
                    control=CTRL_NUMERO;
            end
            A:begin
                    val=5'd10;    
                    control=CTRL_NUMERO;
            end
            B:begin
                    val=5'd11;    
                    control=CTRL_NUMERO;
            end
            C:begin
                    val=5'd12;    
                    control=CTRL_NUMERO;
            end
            D:begin
                    val=5'd13;    
                    control=CTRL_NUMERO;
            end
            E:begin
                    val=5'd14;    
                    control=CTRL_NUMERO;
            end
            F:begin
                    val=5'd15;    
                    control=CTRL_NUMERO;
            end
            SUMA:begin
                    val=5'd21;    
                    control=CTRL_OPERACION;
            end
            RESTA:begin
                    val=5'd22;    
                    control=CTRL_OPERACION;
            end
            MUL:begin
                    val=5'd23;    
                    control=CTRL_OPERACION;
            end
            Y:begin
                    val=5'd24;    
                    control=CTRL_OPERACION;
            end
            O:begin
                    val=5'd25;    
                    control=CTRL_OPERACION;
            end
            ENTER:begin
                    val     =5'd16;    
                    control =CTRL_ENTER;
            end
            ARRIBA:begin
                    val=5'd19;    
                    control=CTRL_FLECHA;
            end
            ABAJO:begin
                    val=5'd20;    
                    control=CTRL_FLECHA;
            end
            IZQUIERDA:begin
                    val=5'd17;    
                    control=CTRL_FLECHA;
            end
            DERECHA:begin
                    val=5'd18;    
                    control=CTRL_FLECHA;
            end
            default: begin
                    val=5'd0;    
                    control=3'd0;
            end
            endcase
    end
    
endmodule
