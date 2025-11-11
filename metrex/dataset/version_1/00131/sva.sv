// SVA checkers and binds for the provided design.
// Focused, concise, and parameterized where applicable.

/////////////////////////////////////////////////////////////
// Adder: functional correctness and X-prop
/////////////////////////////////////////////////////////////
module adder_sva #(parameter WIDTH = 100)
(
  input  [WIDTH-1:0] a, b,
  input              cin,
  input  [WIDTH-1:0] sum,
  input              cout
);
  // Functional equivalence
  assert property (@(*) 1 |-> ##0 ({cout,sum} == a + b + cin));

  // Known outputs when inputs are known
  assert property (@(*) !$isunknown({a,b,cin}) |-> ##0 !$isunknown({sum,cout}));

  // Coverage
  cover property (@(*) cin==0);
  cover property (@(*) cin==1);
  cover property (@(*) cout==1);                 // carry out event
  cover property (@(*) (a=={WIDTH{1'b0}} && b=={WIDTH{1'b0}}));
  cover property (@(*) (&a && b=={WIDTH{1'b0}})); // a=all-ones, b=0
endmodule

bind adder adder_sva #(.WIDTH(WIDTH)) u_adder_sva (.*);

/////////////////////////////////////////////////////////////
// Carry-select adder: structure, muxing, and equivalence
/////////////////////////////////////////////////////////////
module csa_sva #(parameter WIDTH = 100)
(
  input  [WIDTH-1:0] a, b,
  input              cin,
  input  [WIDTH-1:0] sum,
  input              cout,
  // tap internal precompute paths
  input  [WIDTH-1:0] sum0, sum1,
  input              cout0, cout1
);
  // Precompute paths correct
  assert property (@(*) 1 |-> ##0 ({cout0,sum0} == a + b + 1'b0));
  assert property (@(*) 1 |-> ##0 ({cout1,sum1} == a + b + 1'b1));

  // Muxing correct
  assert property (@(*)  cin |-> ##0 (sum==sum1 && cout==cout1));
  assert property (@(*) !cin |-> ##0 (sum==sum0 && cout==cout0));

  // Overall equivalence to ripple addition
  assert property (@(*) 1 |-> ##0 ({cout,sum} == a + b + cin));

  // Known outputs when inputs are known
  assert property (@(*) !$isunknown({a,b,cin}) |-> ##0 !$isunknown({sum,cout}));

  // Coverage
  cover property (@(*) cin==0);
  cover property (@(*) cin==1);
  cover property (@(*) cout==1);
endmodule

bind carry_select_adder
  csa_sva #(.WIDTH(WIDTH)) u_csa_sva (
    .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout),
    .sum0(sum0), .sum1(sum1), .cout0(cout0), .cout1(cout1)
  );

/////////////////////////////////////////////////////////////
// Barrel shifter (rotator): rotate-left by ena[1:0] or load-through
/////////////////////////////////////////////////////////////
module barrel_sva #(parameter WIDTH = 100)
(
  input  [WIDTH-1:0] in,
  input              load,
  input  [1:0]       ena,
  input  [WIDTH-1:0] out
);
  function automatic [WIDTH-1:0] rol(input [WIDTH-1:0] x, input int unsigned s);
    return (x << s) | (x >> (WIDTH - s));
  endfunction

  // Load-through
  assert property (@(*) load |-> ##0 (out == in));

  // Rotate-left by 0..3 when not loading
  assert property (@(*) !load |-> ##0 (out == rol(in, ena)));

  // Known outputs when inputs are known
  assert property (@(*) !$isunknown({in,load,ena}) |-> ##0 !$isunknown(out));

  // Coverage: each rotate amount and load
  cover property (@(*) (load==1));
  cover property (@(*) (!load && ena==2'd0));
  cover property (@(*) (!load && ena==2'd1));
  cover property (@(*) (!load && ena==2'd2));
  cover property (@(*) (!load && ena==2'd3));
endmodule

bind barrel_shifter barrel_sva #(.WIDTH(WIDTH)) u_barrel_sva (.*);

/////////////////////////////////////////////////////////////
// Top-level integration: end-to-end data path checks
/////////////////////////////////////////////////////////////
module top_sva;
  // bind-time only checker (no ports): use hierarchical connections via bind
endmodule

bind top_module top_int_sva u_top_int_sva();

module top_int_sva;
  // Hierarchical refs inside top_module instance scope are not portable; instead,
  // re-bind submodules (done above) and assert top-level relations here via $root.scopes.
  // For portability, re-compute expectations directly using visible ports.
  // Using implicit hierarchical references through bind context:
  // Ports in bound scope:
  wire [99:0] a    = top_module.a;
  wire [99:0] b    = top_module.b;
  wire        cin  = top_module.cin;
  wire [99:0] sum  = top_module.sum;
  wire [99:0] q    = top_module.q;
  wire        load = top_module.load;
  wire [1:0]  ena  = top_module.ena;

  function automatic [99:0] rol100(input [99:0] x, input int unsigned s);
    return (x << s) | (x >> (100 - s));
  endfunction

  // Sum correctness at top
  assert property (@(*) 1 |-> ##0 (sum == (a + b + cin)));

  // Rotator correctness at top
  assert property (@(*) load |-> ##0 (q == sum));
  assert property (@(*) !load |-> ##0 (q == rol100(sum, ena)));

  // Known outputs when inputs are known
  assert property (@(*) !$isunknown({a,b,cin,load,ena}) |-> ##0 !$isunknown({sum,q}));

  // Coverage
  cover property (@(*) (cin==0));
  cover property (@(*) (cin==1));
  cover property (@(*) (load==1));
  cover property (@(*) (!load && ena inside {2'd0,2'd1,2'd2,2'd3}));
endmodule