// SVA for bulletPosition
// Bind module with concise, high-quality checks and coverage

module bulletPosition_sva #(
  parameter int unsigned XMAX = 600,
  parameter int unsigned YMAX = 440
)(
  input  logic               clk,
  input  logic               frameClk,
  input  logic               reset,

  input  logic [9:0]         drawingPositionX,
  input  logic [8:0]         drawingPositionY,
  input  logic [9:0]         characterPositionX,
  input  logic [8:0]         characterPositionY,
  input  logic [1:0]         characterDirection,
  input  logic               _isBulletFire,
  input  logic               isHitEnemy,
  input  logic [4:0]         bulletID,
  input  logic [4:0]         shootingBulletID,

  input  logic               isBulletShooting,
  input  logic               isBulletExistInScreen,
  input  logic [9:0]         bulletPositionX,
  input  logic [8:0]         bulletPositionY,

  // Internal DUT regs (bound to internal names)
  input  logic [1:0]         bulletDirection,
  input  logic [9:0]         diffPositionX,
  input  logic [8:0]         diffPositionY,
  input  logic               recentBulletFire
);

  // Convenience expressions at frameClk domain sample time
  logic fire_cond, move_cond;
  always_comb begin
    fire_cond = (recentBulletFire == 1'b0) && (_isBulletFire == 1'b0) && (bulletID == shootingBulletID);
    move_cond = (isBulletShooting == 1'b1) && (isHitEnemy == 1'b0) &&
                (bulletPositionX > 0) && (bulletPositionX < XMAX) &&
                (bulletPositionY > 0) && (bulletPositionY < YMAX);
  end

  // Reset effects (observed next cycle due to NBA scheduling)
  assert property (@(posedge frameClk) reset |=> (bulletPositionX==10'd0 && bulletPositionY==9'd0 &&
                                                  isBulletShooting==1'b0 && recentBulletFire==1'b0));
  assert property (@(posedge clk)      reset |=> (isBulletExistInScreen==1'b0));

  // Fire capture behavior
  assert property (@(posedge frameClk) disable iff (reset)
    fire_cond |=> (bulletPositionX==characterPositionX && bulletPositionY==characterPositionY &&
                   bulletDirection==characterDirection && recentBulletFire==1'b1 &&
                   isBulletShooting==1'b1));

  // Bullet direction may only change as a result of firing
  assert property (@(posedge frameClk) disable iff (reset)
    (bulletDirection != $past(bulletDirection)) |-> $past(fire_cond));

  // Movement per direction; position updates are 1 LSB per frame, orthogonal axis holds
  assert property (@(posedge frameClk) disable iff (reset)
    (move_cond && bulletDirection==2'b00) |=> (bulletPositionY==$past(bulletPositionY)-1 &&
                                               bulletPositionX==$past(bulletPositionX)   &&
                                               isBulletShooting==1'b1 && recentBulletFire==1'b1));

  assert property (@(posedge frameClk) disable iff (reset)
    (move_cond && bulletDirection==2'b01) |=> (bulletPositionY==$past(bulletPositionY)+1 &&
                                               bulletPositionX==$past(bulletPositionX)   &&
                                               isBulletShooting==1'b1 && recentBulletFire==1'b1));

  assert property (@(posedge frameClk) disable iff (reset)
    (move_cond && bulletDirection==2'b10) |=> (bulletPositionX==$past(bulletPositionX)-1 &&
                                               bulletPositionY==$past(bulletPositionY)   &&
                                               isBulletShooting==1'b1 && recentBulletFire==1'b1));

  assert property (@(posedge frameClk) disable iff (reset)
    (move_cond && bulletDirection==2'b11) |=> (bulletPositionX==$past(bulletPositionX)+1 &&
                                               bulletPositionY==$past(bulletPositionY)   &&
                                               isBulletShooting==1'b1 && recentBulletFire==1'b1));

  // Else branch: clear when neither firing nor moving
  assert property (@(posedge frameClk) disable iff (reset)
    (!fire_cond && !move_cond) |=> (bulletPositionX==10'd0 && bulletPositionY==9'd0 &&
                                    isBulletShooting==1'b0 && recentBulletFire==1'b0));

  // Stop on hit or out-of-bounds: clear next frame
  assert property (@(posedge frameClk) disable iff (reset)
    (isBulletShooting && (isHitEnemy ||
                          !(bulletPositionX>0 && bulletPositionX<XMAX &&
                            bulletPositionY>0 && bulletPositionY<YMAX)))
    |=> (bulletPositionX==10'd0 && bulletPositionY==9'd0 &&
         isBulletShooting==1'b0 && recentBulletFire==1'b0));

  // isBulletShooting only asserted as a consequence of firing or staying asserted
  assert property (@(posedge frameClk) disable iff (reset)
    isBulletShooting |-> ($past(isBulletShooting) || $past(fire_cond)));

  // diffPosition pipeline: 1-cycle delayed function of bullet/drawing positions
  assert property (@(posedge clk) disable iff (reset)
    diffPositionX == $past((bulletPositionX + 10'd4) - drawingPositionX));

  assert property (@(posedge clk) disable iff (reset)
    diffPositionY == $past((bulletPositionY + 9'd4) - drawingPositionY));

  // Screen-existence flag matches previous-cycle diff window check
  assert property (@(posedge clk)
    isBulletExistInScreen ==
      (!$past(reset) && ($past(diffPositionX)>0 && $past(diffPositionX)<7 &&
                         $past(diffPositionY)>0 && $past(diffPositionY)<7)));

  // Coverage
  cover property (@(posedge frameClk) fire_cond);
  cover property (@(posedge frameClk) move_cond && bulletDirection==2'b00);
  cover property (@(posedge frameClk) move_cond && bulletDirection==2'b01);
  cover property (@(posedge frameClk) move_cond && bulletDirection==2'b10);
  cover property (@(posedge frameClk) move_cond && bulletDirection==2'b11);
  cover property (@(posedge frameClk) isBulletShooting && isHitEnemy);          // terminate on hit
  cover property (@(posedge frameClk) isBulletShooting && bulletDirection==2'b11 && bulletPositionX==10'd599); // OOB right
  cover property (@(posedge clk)      isBulletExistInScreen);

endmodule

bind bulletPosition bulletPosition_sva sva_bulletPosition (
  .clk                  (clk),
  .frameClk             (frameClk),
  .reset                (reset),
  .drawingPositionX     (drawingPositionX),
  .drawingPositionY     (drawingPositionY),
  .characterPositionX   (characterPositionX),
  .characterPositionY   (characterPositionY),
  .characterDirection   (characterDirection),
  ._isBulletFire        (_isBulletFire),
  .isHitEnemy           (isHitEnemy),
  .bulletID             (bulletID),
  .shootingBulletID     (shootingBulletID),
  .isBulletShooting     (isBulletShooting),
  .isBulletExistInScreen(isBulletExistInScreen),
  .bulletPositionX      (bulletPositionX),
  .bulletPositionY      (bulletPositionY),
  // Internal connections (allowed in bind scope)
  .bulletDirection      (bulletDirection),
  .diffPositionX        (diffPositionX),
  .diffPositionY        (diffPositionY),
  .recentBulletFire     (recentBulletFire)
);