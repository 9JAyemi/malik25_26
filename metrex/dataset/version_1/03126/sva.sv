// SVA for TrafficSignalController
module TrafficSignalController_sva (
  input logic clk,
  input logic NS_VEHICLE_DETECT,
  input logic EW_VEHICLE_DETECT,
  input logic NS_RED, NS_YELLOW, NS_GREEN,
  input logic EW_RED, EW_YELLOW, EW_GREEN,
  input logic [4:0] count1,
  input logic [3:0] count2,
  input logic [1:0] count3
);

  default clocking cb @(posedge clk); endclocking

  // enable SVA after first clock
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Basic sanity
  assert property (cb !$isunknown({NS_RED,NS_YELLOW,NS_GREEN,EW_RED,EW_YELLOW,EW_GREEN,count1,count2,count3})));

  // One-hot per direction
  assert property (cb $onehot({NS_RED,NS_YELLOW,NS_GREEN}));
  assert property (cb $onehot({EW_RED,EW_YELLOW,EW_GREEN}));
  // Never both greens
  assert property (cb !(NS_GREEN && EW_GREEN));

  // Counter next-state checks
  assert property (cb ($past(count1)==5'd31) |-> (count1==5'd0));
  assert property (cb ($past(count1)!=5'd31) |-> (count1==$past(count1)+5'd1));

  assert property (cb ($past(count3)==2'd3) |-> (count3==2'd0));
  assert property (cb ($past(count3)!=2'd3) |-> (count3==$past(count3)+2'd1));

  assert property (cb ($past(count2)==4'd15) |-> (count2==4'd0));
  assert property (cb ($past(count2)!=4'd15 &&  $past(EW_VEHICLE_DETECT))  |-> (count2==$past(count2)-4'd6));
  assert property (cb ($past(count2)!=4'd15 && !$past(EW_VEHICLE_DETECT))  |-> (count2==$past(count2)+4'd1));

  // Phase decoding (priority: yellow > EW green > NS green > both red)
  wire yellow_phase   = (count3==2'd3);
  wire ew_green_phase = (!yellow_phase && count2==4'd15);
  wire ns_green_phase = (!yellow_phase && !ew_green_phase && count1==5'd31);
  wire red_phase      = (!yellow_phase && !ew_green_phase && !ns_green_phase);

  // Implications: counts -> outputs
  assert property (cb yellow_phase   |-> ( NS_YELLOW && EW_YELLOW && !NS_GREEN && !EW_GREEN && !NS_RED && !EW_RED ));
  assert property (cb ew_green_phase |-> (!NS_YELLOW && !EW_YELLOW && !NS_GREEN &&  EW_GREEN &&  NS_RED && !EW_RED));
  assert property (cb ns_green_phase |-> (!NS_YELLOW && !EW_YELLOW &&  NS_GREEN && !EW_GREEN && !NS_RED &&  EW_RED));
  assert property (cb red_phase      |-> (!NS_YELLOW && !EW_YELLOW && !NS_GREEN && !EW_GREEN &&  NS_RED &&  EW_RED));

  // Equivalences: unique output patterns -> counts/phase
  assert property (cb ( NS_YELLOW && EW_YELLOW && !NS_GREEN && !EW_GREEN && !NS_RED && !EW_RED) <-> yellow_phase);
  assert property (cb (!NS_YELLOW && !EW_YELLOW && !NS_GREEN &&  EW_GREEN &&  NS_RED && !EW_RED) <-> ew_green_phase);
  assert property (cb (!NS_YELLOW && !EW_YELLOW &&  NS_GREEN && !EW_GREEN && !NS_RED &&  EW_RED) <-> ns_green_phase);
  assert property (cb (!NS_YELLOW && !EW_YELLOW && !NS_GREEN && !EW_GREEN &&  NS_RED &&  EW_RED) <-> red_phase);

  // Coverage
  cover property (cb yellow_phase);
  cover property (cb ew_green_phase);
  cover property (cb ns_green_phase);
  cover property (cb red_phase);

  // Priority collision coverage
  cover property (cb (count3==2'd3 && count2==4'd15) &&
                      (NS_YELLOW && EW_YELLOW && !NS_GREEN && !EW_GREEN && !NS_RED && !EW_RED));
  cover property (cb (count2==4'd15 && count1==5'd31 && count3!=2'd3) &&
                      (!NS_YELLOW && !EW_YELLOW && !NS_GREEN &&  EW_GREEN &&  NS_RED && !EW_RED));

  // Wrap/decrement corner coverage
  cover property (cb $past(count1)==5'd31 ##1 count1==5'd0);
  cover property (cb $past(count3)==2'd3  ##1 count3==2'd0);
  cover property (cb $past(count2)==4'd15 ##1 count2==4'd0);
  cover property (cb $past(count2)==4'd2  && $past(EW_VEHICLE_DETECT) ##1 count2==4'd12);

endmodule

// Bind into DUT (accesses internal counters by name)
bind TrafficSignalController TrafficSignalController_sva sva_inst (.*);