// SVA for enemyPosition
// Bind these assertions to your DUT instance:
// bind enemyPosition enemyPosition_sva #( .top(top), .bottom(bottom), .center(center),
//   .left(left), .right(right), .middle(middle), .north(north), .south(south), .west(west), .east(east) ) sva (.*);

module enemyPosition_sva #(
  parameter int top=20,
  parameter int bottom=440,
  parameter int center=220,
  parameter int left=20,
  parameter int right=600,
  parameter int middle=300,
  parameter [1:0] north=2'b00,
  parameter [1:0] south=2'b01,
  parameter [1:0] west =2'b10,
  parameter [1:0] east =2'b11
)(
  input  logic        frameClk,
  input  logic        isEnemyActive,
  input  logic [7:0]  _randomSeed,
  input  logic [3:0]  uid,
  input  logic [9:0]  enemyPositionX,
  input  logic [8:0]  enemyPositionY,
  input  logic [1:0]  enemyDirectionFrom,
  input  logic [1:0]  enemyDirectionTo,
  input  logic        recentEnemyActive,
  input  logic [10:0] randomSeed
);

  default clocking cb @(posedge frameClk); endclocking

  // Basic sanity
  assert property (isEnemyActive |-> (!($isunknown(enemyPositionX) || $isunknown(enemyPositionY))));
  assert property (!isEnemyActive |-> (enemyPositionX==0 && enemyPositionY==0 &&
                                       enemyDirectionFrom==north && enemyDirectionTo==north &&
                                       recentEnemyActive==1'b0));

  // Random seed computation each frame
  assert property (isEnemyActive |-> randomSeed == ({4'b0,_randomSeed[6:0]}*uid)+uid);

  // Initial spawn on activation edge
  // Check directions chosen and border placement rules
  // Also ensure spawn is on an edge consistent with enemyDirectionFrom
  property spawn_p;
    $rose(recentEnemyActive) |-> isEnemyActive &&
    (
      (enemyDirectionFrom==north && enemyPositionY==top+1  &&
         (enemyPositionX == middle + (randomSeed[2:0]*30) ||
          enemyPositionX == middle - (randomSeed[2:0]*30))) ||
      (enemyDirectionFrom==south && enemyPositionY==bottom-1 &&
         (enemyPositionX == middle + (randomSeed[2:0]*30) ||
          enemyPositionX == middle - (randomSeed[2:0]*30))) ||
      (enemyDirectionFrom==west  && enemyPositionX==left+1  &&
         (enemyPositionY == center + (randomSeed[2:0]*25) ||
          enemyPositionY == center - (randomSeed[2:0]*25))) ||
      (enemyDirectionFrom==east  && enemyPositionX==right-1 &&
         (enemyPositionY == center + (randomSeed[2:0]*25) ||
          enemyPositionY == center - (randomSeed[2:0]*25)))
    );
  endproperty
  assert property (spawn_p);

  // Optional: they try to avoid equal directions on spawn (will flag RTL issue if violated)
  assert property ($rose(recentEnemyActive) |-> (enemyDirectionFrom != enemyDirectionTo));

  // Movement when previous position was inside bounds (uses previous dirs)
  function automatic bit inside_box(logic [9:0] x, logic [8:0] y);
    return (x>=left && x<=right && y>=top && y<=bottom);
  endfunction

  // To is vertical: Y steps per 'to'; X steps per 'from' only if 'from' is horizontal
  assert property ( $past(isEnemyActive && recentEnemyActive) &&
                    inside_box($past(enemyPositionX), $past(enemyPositionY)) &&
                    ($past(enemyDirectionTo) inside {north,south})
                    |->
                    enemyPositionY == $past(enemyPositionY) +
                                      (($past(enemyDirectionTo)==north) ? -1 : +1)
                 &&
                    enemyPositionX == $past(enemyPositionX) +
                                      (($past(enemyDirectionFrom) inside {west,east}) ?
                                         (($past(enemyDirectionFrom)==west)? +1 : -1) : 0)
                  );

  // To is horizontal: X steps per 'to'; Y steps per 'from' only if 'from' is vertical
  assert property ( $past(isEnemyActive && recentEnemyActive) &&
                    inside_box($past(enemyPositionX), $past(enemyPositionY)) &&
                    ($past(enemyDirectionTo) inside {west,east})
                    |->
                    enemyPositionX == $past(enemyPositionX) +
                                      (($past(enemyDirectionTo)==west) ? -1 : +1)
                 &&
                    enemyPositionY == $past(enemyPositionY) +
                                      (($past(enemyDirectionFrom) inside {north,south}) ?
                                         (($past(enemyDirectionFrom)==north)? +1 : -1) : 0)
                  );

  // When previous position was outside bounds:
  // Direction rotation: from' == to (previous)
  assert property ( $past(isEnemyActive && recentEnemyActive) &&
                    !inside_box($past(enemyPositionX), $past(enemyPositionY))
                    |-> enemyDirectionFrom == $past(enemyDirectionTo) );

  // Y update outside: if previous 'from' was vertical, Y' = Y +/- 2 (overwrites clamp);
  // otherwise clamp toward/top
  assert property ( $past(isEnemyActive && recentEnemyActive) &&
                    !inside_box($past(enemyPositionX), $past(enemyPositionY))
                    |->
                    ( ($past(enemyDirectionFrom) inside {north,south})
                      ? (enemyPositionY == $past(enemyPositionY) +
                                         (($past(enemyDirectionFrom)==north)? +2 : -2))
                      : (enemyPositionY == ( ($past(enemyPositionY) > top)
                                             ? ($past(enemyPositionY) - 2)
                                             : (top + 2) )) )
                  );

  // X update outside: if previous 'from' was horizontal, X' = X +/- 2 (overwrites clamp);
  // otherwise clamp toward/left
  assert property ( $past(isEnemyActive && recentEnemyActive) &&
                    !inside_box($past(enemyPositionX), $past(enemyPositionY))
                    |->
                    ( ($past(enemyDirectionFrom) inside {west,east})
                      ? (enemyPositionX == $past(enemyPositionX) +
                                         (($past(enemyDirectionFrom)==west)? +2 : -2))
                      : (enemyPositionX == ( ($past(enemyPositionX) > left)
                                             ? ($past(enemyPositionX) - 2)
                                             : (left + 2) )) )
                  );

  // Coverage: see all spawns, directions, branches, orthogonal vs parallel cases
  cover property ($rose(recentEnemyActive));
  cover property ($rose(recentEnemyActive) && enemyDirectionFrom==north);
  cover property ($rose(recentEnemyActive) && enemyDirectionFrom==south);
  cover property ($rose(recentEnemyActive) && enemyDirectionFrom==west);
  cover property ($rose(recentEnemyActive) && enemyDirectionFrom==east);

  cover property ( $past(isEnemyActive && recentEnemyActive) &&
                   inside_box($past(enemyPositionX), $past(enemyPositionY)) );
  cover property ( $past(isEnemyActive && recentEnemyActive) &&
                   !inside_box($past(enemyPositionX), $past(enemyPositionY)) );

  cover property ( $past(isEnemyActive && recentEnemyActive) &&
                   inside_box($past(enemyPositionX), $past(enemyPositionY)) &&
                   ($past(enemyDirectionFrom) inside {north,south}) &&
                   ($past(enemyDirectionTo)   inside {west,east}) );

  cover property ( $past(isEnemyActive && recentEnemyActive) &&
                   inside_box($past(enemyPositionX), $past(enemyPositionY)) &&
                   ($past(enemyDirectionFrom) inside {west,east}) &&
                   ($past(enemyDirectionTo)   inside {north,south}) );

endmodule