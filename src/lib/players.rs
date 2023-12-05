use educe::Educe;
use itertools::Itertools;
use tap::Pipe;

use crate::player::Player;

/// A [`Player`] collection.
#[derive(Educe)]
#[educe(Default)]
pub struct Players(#[educe(Default(expression = "Vec::new()"))] pub Vec<Player>);

impl Players {
    /// Creates a new [`Self`] with the specified `size`, where each [`Player`] has default values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tic_tac_toe_lib::players::Players;
    /// let players = Players::new(2);
    ///
    /// assert_eq!(players.0.get(0).unwrap().mark, "Mark 1");
    /// assert_eq!(players.0.get(0).unwrap().name, "Player 1");
    ///
    /// assert_eq!(players.0.get(1).unwrap().mark, "Mark 2");
    /// assert_eq!(players.0.get(1).unwrap().name, "Player 2");
    /// # Ok::<(), ()>(())
    /// ```
    pub fn new(size: usize) -> Self {
        (1..=size)
            .map(|index| Player {
                mark: format!("Mark {}", index),
                name: format!("Player {}", index),
            })
            .collect_vec()
            .pipe(Players)
    }
}
