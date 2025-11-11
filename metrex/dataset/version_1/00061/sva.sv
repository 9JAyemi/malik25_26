// SVA for bram_controller
// Bind this module to the DUT to check/cover its behavior.

module bram_controller_sva
  #(parameter logic [1:0] IDLE=2'b00, LEER=2'b01, FIN=2'b10)
  (input  logic        clk,
   input  logic        reset,     // async, active-high
   input  logic        btn,
   input  logic        wea,
   input  logic [3:0]  addra,
   input  logic [1:0]  state_reg,
   input  logic [3:0]  counter);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Local started flag to make $past() well-defined after reset
  logic started;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) started <= 1'b0;
    else       started <= 1'b1;
  end

  // Async reset behavior (checked on reset edge)
  assert property (@(posedge reset) 1 |-> (addra==4'd0 && counter==4'd0 && state_reg==IDLE && wea==1'b0));

  // No X/Z on key signals after reset is deasserted
  assert property (started |-> !$isunknown({btn,wea,addra,state_reg,counter}));

  // State encoding legal
  assert property (state_reg inside {IDLE,LEER,FIN});

  // State transitions
  assert property (state_reg==IDLE && !btn |=> state_reg==IDLE);
  assert property (state_reg==IDLE &&  btn |=> state_reg==LEER);
  assert property (state_reg==LEER            |=> state_reg==FIN);
  assert property (state_reg==FIN             |=> state_reg==IDLE);

  // WEA must never assert (DUT drives 0 on reset and in LEER, never sets 1)
  assert property (wea==1'b0);

  // ADDRA behavior: increment only in FIN; hold otherwise
  assert property ((state_reg inside {IDLE,LEER}) |=> $stable(addra));
  assert property (started && state_reg==FIN |=> addra == $past(addra)+4'd1);

  // COUNTER behavior:
  // - increments by 1 in LEER
  // - holds in IDLE
  // - in FIN: wraps to 0 if 15, else holds
  assert property (started && state_reg==LEER |=> counter == $past(counter)+4'd1);
  assert property (state_reg==IDLE            |=> $stable(counter));
  assert property (state_reg==FIN && counter==4'hF |=> counter==4'd0);
  assert property (state_reg==FIN && counter!=4'hF |=> counter==$past(counter));

  // Coverage
  cover property (state_reg==IDLE && btn ##1 state_reg==LEER ##1 state_reg==FIN ##1 state_reg==IDLE);
  cover property (state_reg==FIN && counter==4'hF ##1 counter==4'd0);     // counter wrap
  cover property (state_reg==FIN && addra==4'hF   ##1 addra==4'd0);       // addra wrap

endmodule

// Bind into the DUT (add this in a package or a separate bind file)
bind bram_controller bram_controller_sva
  #(.IDLE(2'b00), .LEER(2'b01), .FIN(2'b10))
  sva_i(.clk(clk),
        .reset(reset),
        .btn(btn),
        .wea(wea),
        .addra(addra),
        .state_reg(state_reg),
        .counter(counter));