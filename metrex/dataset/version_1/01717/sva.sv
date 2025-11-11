// SVA checkers for the given modules. Bind these into the DUTs.
// Concise, combinational properties with essential functional coverage.

//////////////////////////////////////
// reverse
//////////////////////////////////////
module reverse_sva #(parameter width = 1) (
  input  logic [width-1:0] in,
  input  logic [width-1:0] out
);
  // Bit-for-bit reversal
  genvar i;
  generate
    for (i=0; i<width; i++) begin : A
      assert property (@(*) disable iff ($isunknown(in))
        out[i] == in[width-1-i]
      );
    end
  endgenerate

  // Coverage: all-zeros, all-ones
  cover property (@(*) (in=='0) && (out=='0));
  cover property (@(*) (in=={width{1'b1}}) && (out=={width{1'b1}}));
endmodule

bind reverse reverse_sva #(.width(width)) reverse_sva_b (.*);


//////////////////////////////////////
// lowMaskHiLo
// out[k] == (in > bottomBound + k), k in [0..(topBound-bottomBound-1)]
//////////////////////////////////////
module lowMaskHiLo_sva #(
  parameter int inWidth=1,
  parameter int topBound=1,
  parameter int bottomBound=0
) (
  input  logic [inWidth-1:0] in,
  input  logic [topBound-bottomBound-1:0] out
);
  localparam int W = topBound-bottomBound;
  localparam int N = 1<<inWidth;

  // Parameter sanity
  initial begin
    assert (inWidth >= 1);
    assert (topBound > bottomBound);
    assert (topBound <= N);
    assert (bottomBound >= 0);
  end

  // Bit-accurate mask check
  genvar k;
  generate
    for (k=0; k<W; k++) begin : A
      assert property (@(*) disable iff ($isunknown(in))
        out[k] == ($unsigned(in) > (bottomBound + k))
      );
    end
  endgenerate

  // Shape property: ones form a contiguous prefix from LSB upward
  generate
    for (k=0; k<W-1; k++) begin : MONO
      assert property (@(*) disable iff ($isunknown(in))
        out[k+1] |-> out[k]
      );
    end
  endgenerate

  // Extremes
  assert property (@(*) disable iff ($isunknown(in))
    ($unsigned(in) <= bottomBound) |-> (out=='0)
  );
  assert property (@(*) disable iff ($isunknown(in))
    ($unsigned(in) >= topBound)   |-> (out=={W{1'b1}})
  );

  // Coverage: below/inside/above window
  cover property (@(*) ($unsigned(in) <= bottomBound) && (out=='0));
  if (W>1) cover property (@(*) ($unsigned(in) inside {[bottomBound+1:topBound-1]}) && (out!= '0) && (out!= {W{1'b1}}));
  cover property (@(*) ($unsigned(in) >= topBound) && (out=={W{1'b1}}));
endmodule

bind lowMaskHiLo lowMaskHiLo_sva #(.inWidth(inWidth), .topBound(topBound), .bottomBound(bottomBound)) lowMaskHiLo_sva_b (.*);


//////////////////////////////////////
// lowMaskLoHi
// out[k] == (in < bottomBound - k), k in [0..(bottomBound-topBound-1)]
//////////////////////////////////////
module lowMaskLoHi_sva #(
  parameter int inWidth=1,
  parameter int topBound=0,
  parameter int bottomBound=1
) (
  input  logic [inWidth-1:0] in,
  input  logic [bottomBound-topBound-1:0] out
);
  localparam int W = bottomBound-topBound;
  localparam int N = 1<<inWidth;

  // Parameter sanity
  initial begin
    assert (inWidth >= 1);
    assert (bottomBound > topBound);
    assert (bottomBound <= N);
  end

  // Bit-accurate mask check
  genvar k;
  generate
    for (k=0; k<W; k++) begin : A
      assert property (@(*) disable iff ($isunknown(in))
        out[k] == ($unsigned(in) < (bottomBound - k))
      );
    end
  endgenerate

  // Shape property: ones form a contiguous prefix from LSB upward
  generate
    for (k=0; k<W-1; k++) begin : MONO
      assert property (@(*) disable iff ($isunknown(in))
        out[k+1] |-> out[k]
      );
    end
  endgenerate

  // Extremes
  assert property (@(*) disable iff ($isunknown(in))
    ($unsigned(in) >= bottomBound) |-> (out=='0)
  );
  assert property (@(*) disable iff ($isunknown(in))
    ($unsigned(in) <= topBound)    |-> (out=={W{1'b1}})
  );

  // Coverage: below/inside/above window
  cover property (@(*) ($unsigned(in) <= topBound)    && (out=={W{1'b1}}));
  if (W>1) cover property (@(*) ($unsigned(in) inside {[topBound+1:bottomBound-1]}) && (out!= '0) && (out!= {W{1'b1}}));
  cover property (@(*) ($unsigned(in) >= bottomBound) && (out=='0));
endmodule

bind lowMaskLoHi lowMaskLoHi_sva #(.inWidth(inWidth), .topBound(topBound), .bottomBound(bottomBound)) lowMaskLoHi_sva_b (.*);


//////////////////////////////////////
// countLeadingZeros
//////////////////////////////////////
module countLeadingZeros_sva #(
  parameter int inWidth=1,
  parameter int countWidth=1
) (
  input  logic [inWidth-1:0] in,
  input  logic [countWidth-1:0] count
);
  // Parameter sanity
  initial begin
    assert (inWidth >= 1);
    assert ($bits(count) >= $clog2(inWidth+1));
  end

  // In==0 -> count==inWidth
  assert property (@(*) disable iff ($isunknown(in))
    (in=='0) |-> (count == inWidth[countWidth-1:0])
  );

  // For the first 1 from MSB at position i: count == inWidth-1 - i
  genvar i;
  generate
    for (i=inWidth-1; i>=0; i--) begin : CLZ
      if (i==inWidth-1) begin
        assert property (@(*) disable iff ($isunknown(in))
          in[i] |-> (count == (inWidth-1-i)[countWidth-1:0])
        );
      end else begin
        assert property (@(*) disable iff ($isunknown(in))
          (in[inWidth-1:i+1]=='0 && in[i]) |-> (count == (inWidth-1-i)[countWidth-1:0])
        );
      end
    end
  endgenerate

  // Coverage: zero input and single-hot at each bit
  cover property (@(*) (in=='0) && (count==inWidth));
  generate
    for (i=0; i<inWidth; i++) begin : COV1
      cover property (@(*) (in == ({{(inWidth-1){1'b0}},1'b1} << i)) &&
                             (count == (inWidth-1-i)[countWidth-1:0]));
    end
  endgenerate
endmodule

bind countLeadingZeros countLeadingZeros_sva #(.inWidth(inWidth), .countWidth(countWidth)) countLeadingZeros_sva_b (.*);


//////////////////////////////////////
// compressBy2
//////////////////////////////////////
module compressBy2_sva #(parameter int inWidth=1) (
  input  logic [inWidth-1:0] in,
  input  logic [((inWidth - 1)/2):0] out
);
  localparam int R = (inWidth - 1)/2; // maxBitNumReduced
  genvar ix;

  // Main group checks
  generate
    for (ix=0; ix<R; ix++) begin : G
      assert property (@(*) disable iff ($isunknown(in))
        out[ix] == (|in[ix*2 +: 2])
      );
    end
  endgenerate

  // Tail group check
  assert property (@(*) disable iff ($isunknown(in))
    out[R] == (|in[inWidth-1 : R*2])
  );

  // Coverage: group reduces to 0 and to 1
  generate
    for (ix=0; ix<R; ix++) begin : C
      cover property (@(*) (in[ix*2 +: 2] == 2'b00) && (out[ix]==1'b0));
      cover property (@(*) (|in[ix*2 +: 2])            && (out[ix]==1'b1));
    end
  endgenerate
  cover property (@(*) (|in[inWidth-1 : R*2]) && (out[R]==1'b1));
  cover property (@(*) (~|in[inWidth-1 : R*2]) && (out[R]==1'b0));
endmodule

bind compressBy2 compressBy2_sva #(.inWidth(inWidth)) compressBy2_sva_b (.*);


//////////////////////////////////////
// compressBy4
//////////////////////////////////////
module compressBy4_sva #(parameter int inWidth=1) (
  input  logic [inWidth-1:0] in,
  input  logic [(inWidth - 1)/4:0] out
);
  localparam int R = (inWidth - 1)/4; // maxBitNumReduced
  genvar ix;

  // Main group checks
  generate
    for (ix=0; ix<R; ix++) begin : G
      assert property (@(*) disable iff ($isunknown(in))
        out[ix] == (|in[ix*4 +: 4])
      );
    end
  endgenerate

  // Tail group check
  assert property (@(*) disable iff ($isunknown(in))
    out[R] == (|in[inWidth-1 : R*4])
  );

  // Coverage: group reduces to 0 and to 1
  generate
    for (ix=0; ix<R; ix++) begin : C
      cover property (@(*) (~|in[ix*4 +: 4]) && (out[ix]==1'b0));
      cover property (@(*) ( |in[ix*4 +: 4]) && (out[ix]==1'b1));
    end
  endgenerate
  cover property (@(*) (|in[inWidth-1 : R*4]) && (out[R]==1'b1));
  cover property (@(*) (~|in[inWidth-1 : R*4]) && (out[R]==1'b0));
endmodule

bind compressBy4 compressBy4_sva #(.inWidth(inWidth)) compressBy4_sva_b (.*);