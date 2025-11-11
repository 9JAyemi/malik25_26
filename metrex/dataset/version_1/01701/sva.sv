// SVA bind module for MPUC924_383
module MPUC924_383_sva #(parameter int total_bits = 32) (
  input  logic                       CLK,
  input  logic                       DS,
  input  logic                       ED,
  input  logic                       MPYJ,
  input  logic                       C383,
  input  logic signed [total_bits-1:0] DR,
  input  logic signed [total_bits-1:0] DI,

  // internal state
  input  logic                       edd, edd2, edd3,
  input  logic                       mpyjd, mpyjd2, mpyjd3,
  input  logic                       c3d, c3d2, c3d3,
  input  logic       [total_bits-1:0] doo, droo,
  input  logic       [total_bits-1:0] DOR, DOI,
  input  logic signed [total_bits+1:0] dx7,
  input  logic signed [total_bits  :0] dx3,
  input  logic signed [total_bits-1:0] dii,
  input  logic signed [total_bits-1:0] dt,
  input  logic signed [total_bits+1:0] dot
);
  localparam int TB = total_bits;

  default clocking cb @(posedge CLK); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  // Register update only when ED; hold otherwise
  assert property (past_valid && !ED |-> $stable({edd,edd2,edd3,mpyjd,mpyjd2,mpyjd3,c3d,c3d2,c3d3,dx7,dx3,dt,dii,doo,droo,DOR,DOI}));

  // One-cycle ED-qualified pipelines
  assert property (past_valid && ED |=> (edd  == $past(DS)));
  assert property (past_valid && ED |=> (edd2 == $past(edd)));
  assert property (past_valid && ED |=> (edd3 == $past(edd2)));

  assert property (past_valid && ED |=> (mpyjd  == $past(MPYJ)));
  assert property (past_valid && ED |=> (mpyjd2 == $past(mpyjd)));
  assert property (past_valid && ED |=> (mpyjd3 == $past(mpyjd2)));

  assert property (past_valid && ED |=> (c3d  == $past(C383)));
  assert property (past_valid && ED |=> (c3d2 == $past(c3d)));
  assert property (past_valid && ED |=> (c3d3 == $past(c3d2)));

  // Datapath select on DS when ED
  assert property (past_valid && ED && DS |=> (
      dx7 == ( ($signed($past(DR)) << 2) - ($signed($past(DR)) >>> 1) ) &&
      dx3 == (  $signed($past(DR))       + ($signed($past(DR)) >>> 1) ) &&
      dt  ==    $signed($past(DR)) &&
      dii ==    $signed($past(DI))
  ));

  assert property (past_valid && ED && !DS |=> (
      dx7 == ( ($past(dii) << 2) - ($past(dii) >>> 1) ) &&
      dx3 == (  $past(dii)       + ($past(dii) >>> 1) ) &&
      dt  ==    $past(dii) &&
      dii ==    $past(dii)
  ));

  // doo/droo update
  assert property (past_valid && ED |=> doo  == ( ($signed($past(dot)) >>> 2) [TB-1:0] ));
  assert property (past_valid && ED |=> droo == $past(doo));

  // Output update only when ED && edd3; otherwise hold
  assert property (past_valid && ( !ED || (ED && !edd3) ) |-> $stable({DOR,DOI}));

  // Output muxing based on mpyjd3 (note NBA semantics use old doo/droo)
  assert property (past_valid && ED && edd3 && mpyjd3  |=> (DOR == $past(doo)  && DOI == -$past(droo)));
  assert property (past_valid && ED && edd3 && !mpyjd3 |=> (DOR == $past(droo) && DOI ==  $past(doo)));

  // Basic no-X on next-cycle key results when used
  assert property (past_valid && ED |=> !$isunknown({doo,droo}));
  assert property (past_valid && ED && edd3 |=> !$isunknown({DOR,DOI}));

  // Covers (exercise both data/ctrl paths)
  cover property (past_valid && ED && DS);
  cover property (past_valid && ED && !DS);
  cover property (past_valid && ED && (c3d || c3d2));
  cover property (past_valid && ED && !(c3d || c3d2));
  cover property (past_valid && ED && edd3 && mpyjd3);
  cover property (past_valid && ED && edd3 && !mpyjd3);
  // DS launch to edd3 ready through ED-qualified pipeline
  cover property (past_valid && (ED && DS) ##[1:20] (ED) ##[1:20] (ED && edd3));

endmodule

// Bind into the DUT
bind MPUC924_383 MPUC924_383_sva #(.total_bits(total_bits)) MPUC924_383_sva_i (
  .CLK(CLK),
  .DS(DS),
  .ED(ED),
  .MPYJ(MPYJ),
  .C383(C383),
  .DR(DR),
  .DI(DI),

  .edd(edd), .edd2(edd2), .edd3(edd3),
  .mpyjd(mpyjd), .mpyjd2(mpyjd2), .mpyjd3(mpyjd3),
  .c3d(c3d), .c3d2(c3d2), .c3d3(c3d3),
  .doo(doo), .droo(droo),
  .DOR(DOR), .DOI(DOI),
  .dx7(dx7), .dx3(dx3), .dii(dii), .dt(dt),
  .dot(dot)
);