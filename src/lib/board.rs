use array2d::Array2D;
use itertools::Itertools;
use prettytable::Table;
use tap::{Pipe, Tap};
use thiserror::Error;
use tracing;

use crate::{player_index::PlayerIndex, players::Players};

/// [`Board`] related errors.
#[derive(Error, Debug)]
pub enum BoardError {
    /// The [`Board`] size must be strictly positive.
    #[error("Board size must be strictly positive")]
    EmptyBoardError,
}

/// States the [`Board`] may have.
#[derive(Debug, PartialEq)]
pub enum BoardState<'a> {
    /// The [`Board`] is in a drawn state.
    Draw,

    /// The [`Board`] is in progress.
    InProgress,

    /// The [`Board`] has a winner.
    Won(&'a PlayerIndex),
}

/// Generic rectangular [Tic-tac-toe] board of variable size.
///
/// [Tic-tac-toe]: https://en.wikipedia.org/wiki/Tic-tac-toe
pub struct Board(pub Array2D<Option<PlayerIndex>>);
/// Determines the current state of the tic-tac-toe board, indicating whether
/// there is a winner, if the game is a draw, or if it is still in progress.
///
impl Board {
    /// Determines whether the board is in progress, is in a drawn state, or has a winner.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tic_tac_toe_lib::{
    /// #     board::{Board, BoardError, BoardState},
    /// #     player::Player,
    /// #     player_index::PlayerIndex,
    /// #     players::Players,
    /// # };
    /// # let players = Players(vec![Player::default(), Player::default()]);
    /// let mut board = Board::new(3)?;
    ///
    /// board.0.set(0, 2, Some(PlayerIndex(0))).unwrap();
    /// assert_eq!(board.state(), BoardState::InProgress);
    ///
    /// board.0.set(0, 0, Some(PlayerIndex(1))).unwrap();
    /// assert_eq!(board.state(), BoardState::InProgress);
    ///
    /// board.0.set(2, 0, Some(PlayerIndex(0))).unwrap();
    /// assert_eq!(board.state(), BoardState::InProgress);
    ///
    /// board.0.set(1, 1, Some(PlayerIndex(1))).unwrap();
    /// assert_eq!(board.state(), BoardState::InProgress);
    ///
    /// board.0.set(2, 2, Some(PlayerIndex(0))).unwrap();
    /// assert_eq!(board.state(), BoardState::InProgress);
    ///
    /// board.0.set(1, 2, Some(PlayerIndex(1))).unwrap();
    /// assert_eq!(board.state(), BoardState::InProgress);
    ///
    /// board.0.set(2, 1, Some(PlayerIndex(0))).unwrap();
    /// assert_eq!(
    ///     board.state(),
    ///     BoardState::Won(board.0.get(2, 1).unwrap().as_ref().unwrap())
    /// );
    ///
    /// # Ok::<(), BoardError>(())
    /// ```
    pub fn state(&self) -> BoardState {
        if let Some(winner) = self.winner() {
            BoardState::Won(winner)
        } else if self.draw() {
            BoardState::Draw
        } else {
            BoardState::InProgress
        }
    }

    /// Generates a visual representation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tic_tac_toe_lib::{
    /// #     board::{Board, BoardError},
    /// #     player::Player,
    /// #     player_index::PlayerIndex,
    /// #     players::Players,
    /// # };
    /// # let players = Players(vec![Player::default(), Player::default()]);
    /// let mut board = Board::new(3)?;
    ///
    /// board.0.set(0, 0, Some(PlayerIndex(0))).unwrap();
    /// board.0.set(2, 2, Some(PlayerIndex(1))).unwrap();
    ///
    /// assert!(players.0.len() >= 2);
    /// println!("{}", board.display(&players));
    /// # Ok::<(), BoardError>(())
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if one of [`Self`]'s [`PlayerIndex`]es results in a out of bounds lookup in
    /// `players`.
    pub fn display(&self, players: &Players) -> String {
        self.0
            .rows_iter()
            .map(|row| {
                row.map(|element| {
                    element
                        .as_ref()
                        .map_or("", |index| {
                            players
                                .0
                                .get(index.0)
                                .expect(
                                    "Player index should never go out of sync with the players collection"
                                )
                                .mark
                                .as_str()
                        })
                })
            })
            .pipe(Table::from_iter)
            .to_string()
    }

    /// Creates a new [`Self`] with the specified `size`.
    ///
    /// It is recommended to use [`validate_new`] for validating `size`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tic_tac_toe_lib::board::{Board, BoardError};
    /// let mut board = Board::new(3)?;
    /// # Ok::<(), BoardError>(())
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`BoardError`] depending on [`validate_new`].
    ///
    /// [`validate_new`]: Self::validate_new
    #[tracing::instrument]
    pub fn new(size: usize) -> Result<Self, BoardError> {
        Board::validate_new(size).map(|_| Array2D::filled_with(None, size, size).pipe(Self))
    }

    /// Validates [`new`]'s `size` without instantiating [`Self`].
    ///
    /// When [`Self`] is not needed upon success, this function is preferred over [`new`] because
    /// it does not instantiate [`Self`].
    ///
    /// [`new`]: Self::new
    ///
    /// # Examples
    ///
    /// ```
    /// # use tic_tac_toe_lib::board::{Board, BoardError};
    /// # let size = 42;
    /// // On success, 'Board' is instantiated twice.
    /// let slow = Board::new(size)
    ///     .is_ok()
    ///     .then(|| Board::new(size))
    ///     .ok_or_else(|| {
    ///         println!("Invalid board size: {:?}", BoardError::EmptyBoardError);
    ///         BoardError::EmptyBoardError
    ///     })?;
    ///
    /// // On success, 'Board' is instantiated once.
    /// let fast = Board::validate_new(size)
    ///     .is_ok()
    ///     .then(|| Board::new(size))
    ///     .ok_or_else(|| {
    ///         println!("Invalid board size: {:?}", BoardError::EmptyBoardError);
    ///         BoardError::EmptyBoardError
    ///     })?;
    /// # Ok::<(), BoardError>(())
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`BoardError::EmptyBoardError`] if `size` is `0`.
    pub fn validate_new(size: usize) -> Result<(), BoardError> {
        (size != 0)
            .then_some(())
            .ok_or_else(|| BoardError::EmptyBoardError.tap(|error| tracing::info!(?error)))
    }
}

impl Board {
    const EXPECT_IN_BOUND: &'static str = "Should not be out of bound";

    fn draw(&self) -> bool {
        self.0
            .elements_row_major_iter()
            .all(|element| element.is_some())
    }

    fn winner(&self) -> Option<&PlayerIndex> {
        self.winner_row()
            .or_else(|| self.winner_column())
            .or_else(|| self.winner_diagonal())
            .or_else(|| self.winner_anti_diagonal())
    }

    fn winner_anti_diagonal(&self) -> Option<&PlayerIndex> {
        let board_size = self.0.row_len();
        let max_index = board_size - 1;

        (0..board_size)
            .map(|index| {
                self.0
                    .get(index, max_index - index)
                    .expect(Self::EXPECT_IN_BOUND)
            })
            .all_equal_value()
            .ok()
            .unwrap_or(&None)
            .as_ref()
    }

    fn winner_column(&self) -> Option<&PlayerIndex> {
        self.0
            .columns_iter()
            .find_map(|mut column| column.all_equal_value().ok().unwrap_or(&None).as_ref())
    }

    fn winner_diagonal(&self) -> Option<&PlayerIndex> {
        (0..self.0.row_len())
            .map(|index| self.0.get(index, index).expect(Self::EXPECT_IN_BOUND))
            .all_equal_value()
            .ok()
            .unwrap_or(&None)
            .as_ref()
    }

    fn winner_row(&self) -> Option<&PlayerIndex> {
        self.0
            .rows_iter()
            .find_map(|mut row| row.all_equal_value().ok().unwrap_or(&None).as_ref())
    }
}

#[cfg(test)]
mod tests {
    use proptest::proptest;
    use rstest::rstest;

    use super::*;

    #[rstest]
    #[case(1, "+--------+\n| Mark 1 |\n+--------+\n")]
    #[case(
        2,
        "+--------+--+\n| Mark 1 |  |\n+--------+--+\n| Mark 2 |  |\n+--------+--+\n"
    )]
    #[case(
        3,
        "+--------+--------+--------+\n| Mark 1 |        | Mark 2 |\n+--------+--------+--------+\n|        | Mark 3 |        |\n+--------+--------+--------+\n| Mark 4 |        | Mark 5 |\n+--------+--------+--------+\n"
    )]
    fn display_alternatively_filled(#[case] size: usize, #[case] expected: &str) {
        let mut board = Board::new(size).expect(EXPECT_NON_EMPTY_BOARD);
        let players = Players::new(board.0.num_elements() / 2 + 1);

        (0..players.0.len())
            .zip((0..board.0.num_elements()).step_by(2))
            .for_each(|(player_index, board_index)| {
                board
                    .0
                    .set_row_major(board_index, PlayerIndex(player_index).pipe(Some))
                    .expect("'board.0.num_elements()' should never exceed board bounds")
            });

        assert_eq!(board.display(&players), expected);
    }

    #[rstest]
    #[case(1, "+--+\n|  |\n+--+\n")]
    #[case(2, "+--+--+\n|  |  |\n+--+--+\n|  |  |\n+--+--+\n")]
    #[case(
        3,
        "+--+--+--+\n|  |  |  |\n+--+--+--+\n|  |  |  |\n+--+--+--+\n|  |  |  |\n+--+--+--+\n"
    )]
    fn display_empty(#[case] size: usize, #[case] expected: &str) {
        assert_eq!(
            Board::new(size)
                .expect(EXPECT_NON_EMPTY_BOARD)
                .display(&Players::default()),
            expected
        );
    }

    #[rstest]
    #[case(0, false)]
    #[case(1, true)]
    fn new_is_ok(#[case] size: usize, #[case] expected: bool) {
        assert_eq!(Board::new(size).is_ok(), expected);
    }

    proptest! {
        #[test]
        #[should_panic]
        fn display_out_of_bound_player_index(
            size in 1..BOARD_SIZE_UPPER_BOUND,
            player_index: usize,
        ) {
            let mut board = Board::new(size).expect(EXPECT_NON_EMPTY_BOARD);

            board
                .0
                .set(0, 0, PlayerIndex(player_index).pipe(Some))
                .expect(Board::EXPECT_IN_BOUND);

            board.display(&Players::default());
        }

        #[test]
        fn state_draw(size in 2..BOARD_SIZE_UPPER_BOUND) {
            let mut board = Board::new(size).expect(EXPECT_NON_EMPTY_BOARD);

            (0..board.0.num_elements()).for_each(|index| {
                board
                    .0
                    .set_row_major(index, PlayerIndex(index).pipe(Some))
                    .expect(Board::EXPECT_IN_BOUND)
            });

            assert_eq!(board.state(), BoardState::Draw);
        }

        #[test]
        fn state_in_progress(size in 2..BOARD_SIZE_UPPER_BOUND, player_index: usize) {
            let mut board = Board::new(size).expect(EXPECT_NON_EMPTY_BOARD);

            board
                .0
                .set_row_major(size / 2, PlayerIndex(player_index).pipe(Some))
                .expect(Board::EXPECT_IN_BOUND);

            assert_eq!(board.state(), BoardState::InProgress);
        }

        #[test]
        fn state_winner_anti_diagonal(size in 1..BOARD_SIZE_UPPER_BOUND, player_index: usize) {
            let mut board = Board::new(size).expect(EXPECT_NON_EMPTY_BOARD);

            let max_index = board.0.row_len() - 1;

            (0..board.0.row_len()).for_each(|index| {
                board
                    .0
                    .set(index, max_index - index, PlayerIndex(player_index).pipe(Some))
                    .expect(Board::EXPECT_IN_BOUND)
            });

            assert_eq!(
                board.state(),
                board
                    .0
                    .get(0, max_index)
                    .expect(Board::EXPECT_IN_BOUND)
                    .as_ref()
                    .expect(EXPECT_WINNER)
                    .pipe(BoardState::Won)
            );
        }

        #[test]
        fn state_winner_column(size in 1..BOARD_SIZE_UPPER_BOUND, player_index: usize) {
            let mut board = Board::new(size).expect(EXPECT_NON_EMPTY_BOARD);

            let middle = size / 2;

            (0..board.0.column_len()).for_each(|index| {
                board
                    .0
                    .set(index, middle, PlayerIndex(player_index).pipe(Some))
                    .expect(Board::EXPECT_IN_BOUND)
            });

            assert_eq!(
                board.state(),
                board
                    .0
                    .get(0, middle)
                    .expect(Board::EXPECT_IN_BOUND)
                    .as_ref()
                    .expect(EXPECT_WINNER)
                    .pipe(BoardState::Won)
            );
        }

        #[test]
        fn state_winner_diagonal(size in 1..BOARD_SIZE_UPPER_BOUND, player_index: usize) {
            let mut board = Board::new(size).expect(EXPECT_NON_EMPTY_BOARD);

            (0..board.0.row_len()).for_each(|index| {
                board
                    .0
                    .set(index, index, PlayerIndex(player_index).pipe(Some))
                    .expect(Board::EXPECT_IN_BOUND)
            });

            assert_eq!(
                board.state(),
                board
                    .0
                    .get(0, 0)
                    .expect(Board::EXPECT_IN_BOUND)
                    .as_ref()
                    .expect(EXPECT_WINNER)
                    .pipe(BoardState::Won)
            );
        }

        #[test]
        fn state_winner_row(size in 1..BOARD_SIZE_UPPER_BOUND, player_index: usize) {
            let mut board = Board::new(size).expect(EXPECT_NON_EMPTY_BOARD);

            let middle = size / 2;

            (0..board.0.row_len()).for_each(|index| {
                board
                    .0
                    .set(middle, index, PlayerIndex(player_index).pipe(Some))
                    .expect(Board::EXPECT_IN_BOUND)
            });

            assert_eq!(
                board.state(),
                board
                    .0
                    .get(middle, 0)
                    .expect(Board::EXPECT_IN_BOUND)
                    .as_ref()
                    .expect(EXPECT_WINNER)
                    .pipe(BoardState::Won)
            );
        }
    }

    const BOARD_SIZE_UPPER_BOUND: usize = 100;
    const EXPECT_NON_EMPTY_BOARD: &str = "Board size is strictly positive";
    const EXPECT_WINNER: &str = "Should contain the winner";
}
