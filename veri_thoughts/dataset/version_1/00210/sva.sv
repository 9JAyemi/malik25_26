// SVA for draw_block – concise, high-quality checks and coverage
module draw_block_sva #(parameter int LEFT=160, TOP=0, MAXX=320, MAXY=480)
(
  input  logic        clock,
  input  logic [10:0] vcounter,
  input  logic [11:0] hcounter,
  input  logic [2:0]  block,
  input  logic [4:0]  sel_row, sel_col,
  input  logic [3:0]  out,
  input  logic        rev
);

  default clocking cb @(posedge clock); endclocking

  // Geometry helpers
  let IN_RANGE = (hcounter >= LEFT) && (hcounter < LEFT+MAXX) &&
                 (vcounter >= TOP)  && (vcounter < TOP+MAXY);

  // Gate % to avoid negative evaluation when not in-range
  let I = IN_RANGE ? ((hcounter-LEFT)%32) : 0;
  let J = IN_RANGE ? ((vcounter-TOP)%16)  : 0;

  let BORDER = (I==0 || I==31 || J==0 || J==15);
  let MID_I  = (I>8 && I<23);
  let RAIL_I = (I==8 || I==23);

  function automatic logic [3:0] map_low2 (input logic [1:0] b);
    case (b) 2'b00: map_low2=4'b0000; 2'b01: map_low2=4'b1100;
             2'b10: map_low2=4'b1011; 2'b11: map_low2=4'b1101; endcase
  endfunction
  function automatic logic [3:0] map_high2(input logic [1:0] b);
    case (b) 2'b00: map_high2=4'b1001; 2'b01: map_high2=4'b1010;
             2'b10: map_high2=4'b1110; 2'b11: map_high2=4'b1111; endcase
  endfunction

  function automatic logic [3:0] exp_out(input bit in_r, input logic [2:0] b, input int i, input int j);
    if (!in_r)                       exp_out = 4'b0000;
    else if (b == 3'b000)            exp_out = 4'b0000;
    else if (!b[2]) begin
      if (i>8 && i<23)               exp_out = ((j==0||j==15) ? 4'b1000 : map_low2(b[1:0]));
      else if (i==8 || i==23)        exp_out = 4'b1000;
      else if (b[1:0]==2'b11)        exp_out = ((i==0||i==31||j==0||j==15) ? 4'b1000 : 4'b1110);
      else                           exp_out = 4'b0000;
    end else begin
      if (i==0 || i==31 || j==0 || j==15) exp_out = 4'b1000;
      else                                 exp_out = map_high2(b[1:0]);
    end
  endfunction

  // Core functional equivalence
  assert property (out == exp_out(IN_RANGE, block, I, J))
    else $error("draw_block out mismatch: in_range=%0b block=%0b I=%0d J=%0d out=%0b exp=%0b",
                IN_RANGE, block, I, J, out, exp_out(IN_RANGE, block, I, J));

  // Indexing correctness within drawable area
  assert property (IN_RANGE |-> (sel_col == ((hcounter-LEFT)/32) && sel_row == ((vcounter-TOP)/16)));
  assert property (IN_RANGE |-> (sel_col <= (MAXX/32-1) && sel_row <= (MAXY/16-1)));

  // Legal value set guard when drawing (non-000 block)
  assert property (IN_RANGE && block!=3'b000 |-> out inside {4'b0000,4'b1000,4'b1001,4'b1010,4'b1011,4'b1100,4'b1101,4'b1110,4'b1111});

  // rev must toggle every cycle once initialized
  assert property (!$isunknown($past(rev)) |-> rev == ~$past(rev));

  // Coverage: key branches, edges, and pattern values
  cover property (!IN_RANGE && out==4'b0000);
  cover property (IN_RANGE && block==3'b000 && out==4'b0000);

  // ~block[2] mid strip, interior rows for each low2 mapping
  cover property (IN_RANGE && !block[2] && MID_I && J inside {[1:14]} && block[1:0]==2'b00 && out==4'b0000);
  cover property (IN_RANGE && !block[2] && MID_I && J inside {[1:14]} && block[1:0]==2'b01 && out==4'b1100);
  cover property (IN_RANGE && !block[2] && MID_I && J inside {[1:14]} && block[1:0]==2'b10 && out==4'b1011);
  cover property (IN_RANGE && !block[2] && MID_I && J inside {[1:14]} && block[1:0]==2'b11 && out==4'b1101);

  // ~block[2] borders/rails and 2'b11 outer region behavior
  cover property (IN_RANGE && !block[2] && MID_I && (J==0 || J==15) && out==4'b1000);
  cover property (IN_RANGE && !block[2] && RAIL_I && out==4'b1000);
  cover property (IN_RANGE && !block[2] && !MID_I && !RAIL_I && block[1:0]==2'b11 && !BORDER && out==4'b1110);
  cover property (IN_RANGE && !block[2] && !MID_I && !RAIL_I && block[1:0]==2'b11 &&  BORDER && out==4'b1000);

  // block[2]==1 borders and each inner mapping
  cover property (IN_RANGE &&  block[2] &&  BORDER && out==4'b1000);
  cover property (IN_RANGE &&  block[2] && !BORDER && block[1:0]==2'b00 && out==4'b1001);
  cover property (IN_RANGE &&  block[2] && !BORDER && block[1:0]==2'b01 && out==4'b1010);
  cover property (IN_RANGE &&  block[2] && !BORDER && block[1:0]==2'b10 && out==4'b1110);
  cover property (IN_RANGE &&  block[2] && !BORDER && block[1:0]==2'b11 && out==4'b1111);

  // Extremal selection bins
  cover property (IN_RANGE && sel_col==0 && sel_row==0);
  cover property (IN_RANGE && sel_col==(MAXX/32-1) && sel_row==(MAXY/16-1));
endmodule

// Bind SVA to the DUT (access internal rev via bind connection)
bind draw_block draw_block_sva #(.LEFT(LEFT), .TOP(TOP), .MAXX(MAXX), .MAXY(MAXY))
  u_draw_block_sva(.clock(clock), .vcounter(vcounter), .hcounter(hcounter),
                   .block(block), .sel_row(sel_row), .sel_col(sel_col), .out(out), .rev(rev));